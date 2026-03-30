(ns clua.stdlib.string
  "Lua string library implementation.

   Implements Lua 5.3 string functions including pattern matching.
   Lua patterns are NOT regular expressions - they have their own syntax:

   Character classes:
     .  - any character
     %a - letters (A-Za-z)
     %c - control characters
     %d - digits (0-9)
     %g - printable characters except space
     %l - lowercase letters
     %p - punctuation
     %s - whitespace
     %u - uppercase letters
     %w - alphanumeric (A-Za-z0-9)
     %x - hexadecimal digits
     %z - the null character (\\0)
     %X - (where X is any non-alphanumeric) represents X itself

   Pattern items:
     *     - 0 or more (greedy)
     +     - 1 or more (greedy)
     -     - 0 or more (lazy/shortest)
     ?     - 0 or 1
     [set] - character class (e.g., [abc], [a-z], [^abc])
     %bxy  - balanced match between x and y
     ()    - capture
     %n    - back reference to capture n (1-9)

   Anchors:
     ^  - anchor at start (only at pattern start)
     $  - anchor at end (only at pattern end)"
  (:require [clojure.string :as str]
            [clua.interpreter.coro-runtime :as coro]
            [clua.interpreter.env :as env]
            [clua.interpreter.api :as interp]
            [clua.interpreter.operators :as ops]
            [clua.interpreter.tables :as tables])
  (:import (java.math BigInteger)
           (java.nio ByteBuffer ByteOrder)
           (java.util.concurrent ConcurrentHashMap)
           (java.util.concurrent.atomic AtomicLong)))

(set! *warn-on-reflection* true)

;; Short-string threshold: Lua interns strings shorter than LUAI_MAXSHORTLEN (40 bytes).
;; For %p format, we simulate this by assigning stable content-based IDs to short strings
;; so that equal short strings always produce the same %p address.
;; Long strings (>= 40) use System/identityHashCode, which differs per object.
(def ^:private ^ConcurrentHashMap short-str-ids
  (ConcurrentHashMap.))
(def ^:private ^AtomicLong short-str-counter
  (AtomicLong.))

(defn- short-str-ptr
  "Return a stable numeric ID for short string s (used for %p formatting)."
  [^String s]
  (or (.get short-str-ids s)
      (let [new-id (.incrementAndGet short-str-counter)
            winner (.putIfAbsent short-str-ids s new-id)]
        (or winner new-id))))

(defn- check-integer-arg
  "Coerce a number to long for use as a string function argument.
   Throws 'number has no integer representation' if n is a float without exact integer value.
   Returns the long value."
  [n arg-n fn-name]
  (if (integer? n)
    (long n)
    (let [coerced (ops/coerce-bitwise n)]
      (if (some? coerced)
        (long coerced)
        (throw (ex-info (str "bad argument #" arg-n " to '" fn-name
                             "' (number has no integer representation)")
                        {:type :error}))))))

;; =============================================================================
;; Custom Lua Pattern Matching Engine
;; Based on PUC-Lua 5.3 lstrlib.c pattern matching algorithm
;; =============================================================================

(defn- match-class?
  "Test if byte value c (0-255, as long) matches Lua character class letter cc.
   Uppercase cc = complement of lowercase. Uses C-locale ASCII-only semantics."
  [^long c cc]
  (let [lcc (Character/toLowerCase ^char cc)
        result (case lcc
                 \a (or (and (>= c 65) (<= c 90))
                        (and (>= c 97) (<= c 122)))
                 \c (or (< c 32) (= c 127))
                 \d (and (>= c 48) (<= c 57))
                 \g (and (>= c 33) (<= c 126))
                 \l (and (>= c 97) (<= c 122))
                 \p (and (>= c 33) (<= c 126)
                         (not (or (and (>= c 48) (<= c 57))
                                  (and (>= c 65) (<= c 90))
                                  (and (>= c 97) (<= c 122)))))
                 \s (#{9 10 11 12 13 32} c)
                 \u (and (>= c 65) (<= c 90))
                 \w (or (and (>= c 65) (<= c 90))
                        (and (>= c 97) (<= c 122))
                        (and (>= c 48) (<= c 57)))
                 \x (or (and (>= c 48) (<= c 57))
                        (and (>= c 65) (<= c 70))
                        (and (>= c 97) (<= c 102)))
                 \z (= c 0)
                 (= c (int cc)))]
    (if (Character/isUpperCase ^char cc) (not result) result)))

(defn- set-end
  "Return index just past the closing ] of set starting at p[pi] = '['.
   Throws 'malformed pattern (missing ']')' if set is never closed."
  [^String p ^long pi ^long plen]
  (let [i1 (unchecked-inc pi)
        i2 (long (if (and (< i1 plen) (= \^ (nth p i1))) (unchecked-inc i1) i1))
        content-start i2]
    (loop [i (long (if (and (< content-start plen) (= \] (nth p content-start)))
                     (unchecked-inc content-start)
                     content-start))]
      (cond
        (>= i plen)
        (throw (ex-info "malformed pattern (missing ']')" {:type :error}))
        (= \] (nth p i))
        (unchecked-inc i)
        (and (= \% (nth p i)) (< (unchecked-inc i) plen))
        (recur (unchecked-add i 2))
        :else
        (recur (unchecked-inc i))))))

(defn- match-set?
  "Test if byte value c matches character set p[pi..] where p[pi] = '['."
  [^long c ^String p ^long pi ^long plen]
  (let [i1 (unchecked-inc pi)
        negated? (and (< i1 plen) (= \^ (nth p i1)))
        content-start (long (if negated? (unchecked-inc i1) i1))
        close-pos (long (loop [i (long (if (and (< content-start plen) (= \] (nth p content-start)))
                                         (unchecked-inc content-start)
                                         content-start))]
                          (cond
                            (>= i plen) plen
                            (= \] (nth p i)) i
                            (and (= \% (nth p i)) (< (unchecked-inc i) plen)) (recur (unchecked-add i 2))
                            :else (recur (unchecked-inc i)))))
        found? (loop [i content-start]
                 (cond
                   (>= i close-pos) false
                   (and (= \% (nth p i)) (< (unchecked-inc i) close-pos))
                   (if (match-class? c (nth p (unchecked-inc i)))
                     true
                     (recur (unchecked-add i 2)))
                   (and (< (unchecked-add i 2) close-pos) (= \- (nth p (unchecked-inc i))))
                   (let [from (int (nth p i))
                         to (int (nth p (unchecked-add i 2)))]
                     (if (and (>= c from) (<= c to))
                       true
                       (recur (unchecked-add i 3))))
                   :else
                   (if (= c (int (nth p i)))
                     true
                     (recur (unchecked-inc i)))))]
    (if negated? (not found?) found?)))

(defn- item-size
  "Return how many pattern chars a single unquantified item at p[pi] occupies."
  [^String p ^long pi ^long plen]
  (case (nth p pi)
    \% 2
    \[ (unchecked-subtract (long (set-end p pi plen)) pi)
    1))

(defn- single-match?
  "Test if s[si] matches the single pattern item at p[pi]."
  [s slen p plen si pi]
  (let [slen (long slen) si (long si) pi (long pi) plen (long plen)]
    (when (< si slen)
      (let [c (int (nth s si))]
        (case (nth p pi)
          \. true
          \% (match-class? c (nth p (unchecked-inc pi)))
          \[ (match-set? c p pi plen)
          (= c (int (nth p pi))))))))

(defn- match-balance
  "For %bxy: match balanced open/close chars starting at si.
   Checks close char before open char (matches PUC-Lua for open==close case).
   Returns new si (past balanced sequence) or nil."
  [s slen si open close]
  (let [slen (long slen) si (long si) open (long open) close (long close)]
    (when (and (< si slen) (= (int (nth s si)) open))
      (loop [si (unchecked-inc si) count (long 1)]
        (when (< si slen)
          (let [ch (int (nth s si))]
            (cond
              (= ch close) (if (= count 1)
                             (unchecked-inc si)
                             (recur (unchecked-inc si) (unchecked-dec count)))
              (= ch open) (recur (unchecked-inc si) (unchecked-inc count))
              :else (recur (unchecked-inc si) count))))))))

(declare pattern-match)

(defn- match-greedy
  "Greedy quantifier: count max matches of item p[pi], try from max down to min-count."
  [s slen p plen si pi caps depth next-pi min-count]
  (let [slen (long slen) si (long si) pi (long pi) plen (long plen)
        depth (long depth) next-pi (long next-pi) min-count (long min-count)
        max-count (long (loop [cnt (long 0)]
                          (if (single-match? s slen p plen (unchecked-add si cnt) pi)
                            (recur (unchecked-inc cnt))
                            cnt)))]
    (loop [count max-count]
      (when (>= count min-count)
        (let [r (pattern-match s slen p plen (unchecked-add si count) next-pi caps (unchecked-inc depth))]
          (if r r (recur (unchecked-dec count))))))))

(defn- match-lazy
  "Lazy quantifier: try rest of pattern before consuming more chars."
  [s slen p plen si pi caps depth next-pi]
  (let [slen (long slen) pi (long pi) plen (long plen)
        depth (long depth) next-pi (long next-pi)]
    (loop [si (long si)]
      (let [r (pattern-match s slen p plen si next-pi caps (unchecked-inc depth))]
        (if r
          r
          (when (single-match? s slen p plen si pi)
            (recur (unchecked-inc si))))))))

(defn- pattern-match
  "Core recursive Lua pattern matcher.
   Returns [end-si caps-vec] on success, nil on failure."
  [s slen p plen si pi caps depth]
  (let [slen (long slen) si (long si) pi (long pi) plen (long plen) depth (long depth)]
    (when (> depth 200)
      (throw (ex-info "pattern too complex" {:type :error})))
    (cond
      ;; End of pattern — success (check for unclosed captures)
      (>= pi plen)
      (do (when (some #(= :open (:len %)) caps)
            (throw (ex-info "unfinished capture" {:type :error})))
          [si caps])

      ;; $ at end of pattern — anchor to string end
      (and (= \$ (nth p pi)) (= pi (unchecked-dec plen)))
      (when (= si slen)
        [si caps])

      ;; ( — open capture or position capture
      (= \( (nth p pi))
      (let [npi (unchecked-inc pi)]
        (if (and (< npi plen) (= \) (nth p npi)))
          (pattern-match s slen p plen si (unchecked-add pi 2)
                         (conj caps {:start si :len :pos}) (unchecked-inc depth))
          (pattern-match s slen p plen si npi
                         (conj caps {:start si :len :open}) (unchecked-inc depth))))

      ;; ) — close most recent open capture
      (= \) (nth p pi))
      (let [last-open (loop [i (unchecked-dec (count caps))]
                        (when (>= i 0)
                          (if (= :open (:len (nth caps i)))
                            i
                            (recur (unchecked-dec i)))))]
        (when (nil? last-open)
          (throw (ex-info "invalid pattern capture" {:type :error})))
        (let [cap (nth caps last-open)
              new-cap (assoc cap :len (unchecked-subtract si (long (:start cap))))
              new-caps (assoc caps last-open new-cap)]
          (pattern-match s slen p plen si (unchecked-inc pi) new-caps (unchecked-inc depth))))

      ;; % — escape sequences
      (= \% (nth p pi))
      (cond
        (>= (unchecked-inc pi) plen)
        (throw (ex-info "malformed pattern (ends with '%')" {:type :error}))

        ;; %b — balanced match
        (= \b (nth p (unchecked-inc pi)))
        (if (< (unchecked-add pi 3) plen)
          (let [open (int (nth p (unchecked-add pi 2)))
                close (int (nth p (unchecked-add pi 3)))
                nsi (match-balance s slen si open close)]
            (when nsi
              (pattern-match s slen p plen nsi (unchecked-add pi 4) caps (unchecked-inc depth))))
          (throw (ex-info "malformed pattern (missing arguments to '%b')" {:type :error})))

        ;; %f — frontier pattern
        (= \f (nth p (unchecked-inc pi)))
        (if (and (< (unchecked-add pi 2) plen) (= \[ (nth p (unchecked-add pi 2))))
          (let [set-pi (unchecked-add pi 2)
                prev-c (long (if (> si 0) (int (nth s (unchecked-dec si))) 0))
                curr-c (long (if (< si slen) (int (nth s si)) 0))]
            (when (and (not (match-set? prev-c p set-pi plen))
                       (match-set? curr-c p set-pi plen))
              (pattern-match s slen p plen si (set-end p set-pi plen) caps (unchecked-inc depth))))
          (throw (ex-info "missing '[' after '%f' in pattern" {:type :error})))

        ;; %N — back-reference (N = 1-9)
        (Character/isDigit ^char (nth p (unchecked-inc pi)))
        (let [n (long (Character/digit ^char (nth p (unchecked-inc pi)) 10))]
          (cond
            (zero? n)
            (throw (ex-info "invalid capture index %0" {:type :error}))
            (> n (count caps))
            (throw (ex-info (str "invalid capture index %" n) {:type :error}))
            :else
            (let [cap (nth caps (unchecked-dec n))
                  clen (:len cap)]
              (when (or (= clen :open) (= clen :pos))
                (throw (ex-info (str "invalid capture index %" n) {:type :error})))
              (let [clen (long clen)
                    cstart (long (:start cap))
                    cap-text (subs s cstart (unchecked-add cstart clen))]
                (when (and (<= (unchecked-add si clen) slen)
                           (= cap-text (subs s si (unchecked-add si clen))))
                  (pattern-match s slen p plen (unchecked-add si clen) (unchecked-add pi 2) caps (unchecked-inc depth)))))))

        ;; %X — literal escape or char class; single item of size 2
        :else
        (let [next-pi (unchecked-add pi 2)]
          (if (< next-pi plen)
            (case (nth p next-pi)
              \* (match-greedy s slen p plen si pi caps depth (unchecked-inc next-pi) 0)
              \+ (match-greedy s slen p plen si pi caps depth (unchecked-inc next-pi) 1)
              \- (match-lazy s slen p plen si pi caps depth (unchecked-inc next-pi))
              \? (or (when (single-match? s slen p plen si pi)
                       (pattern-match s slen p plen (unchecked-inc si) (unchecked-inc next-pi) caps (unchecked-inc depth)))
                     (pattern-match s slen p plen si (unchecked-inc next-pi) caps (unchecked-inc depth)))
              ;; tail-recursive: linear advance, no backtracking — don't increment depth
              (when (single-match? s slen p plen si pi)
                (pattern-match s slen p plen (unchecked-inc si) next-pi caps depth)))
            (when (single-match? s slen p plen si pi)
              (pattern-match s slen p plen (unchecked-inc si) next-pi caps depth)))))

      ;; [ — character set
      (= \[ (nth p pi))
      (let [isz (long (item-size p pi plen))
            next-pi (unchecked-add pi isz)]
        (if (< next-pi plen)
          (case (nth p next-pi)
            \* (match-greedy s slen p plen si pi caps depth (unchecked-inc next-pi) 0)
            \+ (match-greedy s slen p plen si pi caps depth (unchecked-inc next-pi) 1)
            \- (match-lazy s slen p plen si pi caps depth (unchecked-inc next-pi))
            \? (or (when (single-match? s slen p plen si pi)
                     (pattern-match s slen p plen (unchecked-inc si) (unchecked-inc next-pi) caps (unchecked-inc depth)))
                   (pattern-match s slen p plen si (unchecked-inc next-pi) caps (unchecked-inc depth)))
            ;; tail-recursive: linear advance, no backtracking — don't increment depth
            (when (single-match? s slen p plen si pi)
              (pattern-match s slen p plen (unchecked-inc si) next-pi caps depth)))
          (when (single-match? s slen p plen si pi)
            (pattern-match s slen p plen (unchecked-inc si) next-pi caps depth))))

      ;; Single character (including . handled in single-match?)
      :else
      (let [next-pi (unchecked-inc pi)]
        (if (< next-pi plen)
          (case (nth p next-pi)
            \* (match-greedy s slen p plen si pi caps depth (unchecked-inc next-pi) 0)
            \+ (match-greedy s slen p plen si pi caps depth (unchecked-inc next-pi) 1)
            \- (match-lazy s slen p plen si pi caps depth (unchecked-inc next-pi))
            \? (or (when (single-match? s slen p plen si pi)
                     (pattern-match s slen p plen (unchecked-inc si) (unchecked-inc next-pi) caps (unchecked-inc depth)))
                   (pattern-match s slen p plen si (unchecked-inc next-pi) caps (unchecked-inc depth)))
            ;; tail-recursive: linear advance, no backtracking — don't increment depth
            (when (single-match? s slen p plen si pi)
              (pattern-match s slen p plen (unchecked-inc si) next-pi caps depth)))
          (when (single-match? s slen p plen si pi)
            (pattern-match s slen p plen (unchecked-inc si) next-pi caps depth)))))))

(defn- lua-pattern-find
  "Find first match of pattern p in string s starting at 0-based position si.
   Handles ^ anchor. Returns {:start :end :caps} or nil."
  [s p si]
  (let [slen (long (count s))
        plen (long (count p))
        anchored (and (pos? plen) (= \^ (nth p 0)))
        pi (long (if anchored 1 0))]
    (loop [try-si (long si)]
      (let [r (pattern-match s slen p plen try-si pi [] 0)]
        (if r
          {:start try-si :end (first r) :caps (second r)}
          (if (or anchored (>= try-si slen))
            nil
            (recur (unchecked-inc try-si))))))))

(defn- extract-cap-values
  "Convert internal caps vector to user-visible values (text strings or 1-based positions)."
  [s caps]
  (mapv (fn [{:keys [start len]}]
          (case len
            :pos (unchecked-inc (long start))
            :open (throw (ex-info "unfinished capture" {:type :error}))
            (let [st (long start) ln (long len)] (subs s st (unchecked-add st ln)))))
        caps))

;; =============================================================================
;; String Library Functions
;; =============================================================================

(defn- check-string-coerce
  "Return s as a string, coercing numbers. Throw for other types.
   Mirrors Lua 5.3 luaL_checkstring: strings and numbers are accepted,
   everything else throws 'bad argument #N to FN (string expected, got TYPE)'."
  [s arg-n fn-name]
  (cond
    (string? s) s
    (number? s) (str s)
    :else (throw (ex-info (str "bad argument #" arg-n " to '" fn-name
                               "' (string expected, got " (interp/lua-type s) ")")
                          {:type :error}))))

(defn lua-len
  "string.len(s) - Returns the length of string s."
  [s]
  (count (str s)))

(defn lua-sub
  "string.sub(s, i [, j]) - Returns substring from i to j (1-indexed, inclusive).
   Negative indices count from end."
  [s & [i j]]
  ;; Type check s: must be a string
  (when-not (string? s)
    (if env/*in-method-call*
      (throw (ex-info (str "calling 'sub' on bad self (string expected, got " (interp/lua-type s) ")")
                      {:type :error}))
      (throw (ex-info (str "bad argument #1 to 'sub' (string expected, got " (interp/lua-type s) ")")
                      {:type :error}))))
  ;; Type check i: must be an integer-representable number
  (when (some? i)
    (let [arg-n (if env/*in-method-call* 1 2)]
      (if (not (number? i))
        (throw (ex-info (str "bad argument #" arg-n " to 'sub' (number expected, got " (interp/lua-type i) ")")
                        {:type :error}))
        (check-integer-arg i arg-n "sub"))))
  ;; Type check j: must be an integer-representable number if provided
  (when (some? j)
    (let [arg-n (if env/*in-method-call* 2 3)]
      (if (not (number? j))
        (throw (ex-info (str "bad argument #" arg-n " to 'sub' (number expected, got " (interp/lua-type j) ")")
                        {:type :error}))
        (check-integer-arg j arg-n "sub"))))
  (let [len (count s)
        normalize (fn [idx default]
                    (let [idx (or idx default)
                          idx (long idx)
                          idx (if (neg? idx) (+ len idx 1) idx)]
                      idx))
        i (long (normalize i 1))
        j (long (normalize j len))
        start (long (max 0 (unchecked-dec i)))
        end (long (min len j))]
    (if (> start end)
      ""
      (subs s start end))))

(defn lua-upper
  "string.upper(s) - Returns s with all lowercase letters converted to uppercase."
  [s]
  (.toUpperCase (str s)))

(defn lua-lower
  "string.lower(s) - Returns s with all uppercase letters converted to lowercase."
  [s]
  (.toLowerCase (str s)))

(defn lua-rep
  "string.rep(s, n [, sep]) - Returns n copies of s concatenated with sep."
  [s n & [sep]]
  (let [n (long (check-integer-arg n (if env/*in-method-call* 1 2) "rep"))
        s (str s)
        sep (or sep "")
        s-len (long (count s))
        sep-len (long (count sep))
        max-size (long 100000000)]
    (cond
      (< n 0) (throw (ex-info "invalid value" {:type :error}))
      (= n 0) ""
      ;; Check if result would be too large (prevent OOM)
      ;; Avoid overflow by checking n > max-size / (s-len + sep-len)
      (and (pos? (unchecked-add s-len sep-len))
           (> n (quot max-size (unchecked-add s-len sep-len))))
      (throw (ex-info "resulting string too large" {:type :error}))
      :else
      (str/join sep (repeat n s)))))

(defn lua-byte
  "string.byte(s [, i [, j]]) - Returns numeric codes of characters s[i] through s[j]."
  [s & [i j]]
  (let [s (str s)
        len (long (count s))
        i (long (or i 1))
        j (long (or j i))
        ;; Handle negative indices
        i (long (if (neg? i) (+ len i 1) i))
        j (long (if (neg? j) (+ len j 1) j))
        ;; Clamp
        start (long (max 0 (unchecked-dec i)))
        end (long (min len j))]
    (if (> start end)
      nil
      (let [codes (mapv int (subs s start end))]
        (if (= 1 (count codes))
          (first codes)
          codes)))))

(defn lua-char
  "string.char(...) - Returns a string from numeric character codes.
   Each code must be in [0, 255]; throws 'value out of range' otherwise."
  [& codes]
  (doseq [[i code] (map-indexed vector codes)]
    (let [n (long code)]
      (when (or (< n 0) (> n 255))
        (throw (ex-info (str "bad argument #" (unchecked-inc (long i)) " to 'char' (value out of range)")
                        {:type :error})))))
  (apply str (map char codes)))

(defn lua-reverse
  "string.reverse(s) - Returns s reversed."
  [s]
  (apply str (reverse (str s))))

(defn- quote-string
  "Quote a string for Lua source code (%q format).
   Uses letter escapes for common control chars (\\n, \\t, etc) and decimal for others.
   Uses 3-digit form when next char is a digit to avoid ambiguity."
  [s]
  (let [s (str s)
        len (count s)
        result (StringBuilder.)]
    (.append result "\"")
    (loop [i 0]
      (when (< i len)
        (let [c (nth s i)
              next-is-digit? (and (< (inc i) len)
                                  (Character/isDigit (int (nth s (inc i)))))]
          (cond
            ;; Quote needs escaping as \"
            (= c \") (.append result "\\\"")
            ;; Backslash needs escaping as \\
            (= c \\) (.append result "\\\\")
            ;; Newline: use backslash + actual newline (supported by ANTLR grammar)
            (= c \newline) (.append result "\\\n")          ; backslash + actual newline byte
            ;; Other control chars: use letter escapes (ANTLR requires these)
            (= c \return) (.append result "\\r")            ; \r (two chars: backslash + 'r')
            (= c \tab) (.append result "\\t")               ; \t (two chars: backslash + 't')
            ;; Other control characters use decimal escapes
            (< (int c) 32)
            ;; Use 3-digit form if next char is a digit, to avoid ambiguity
            (if next-is-digit?
              (.append result (format "\\%03d" (int c)))
              (.append result (format "\\%d" (int c))))
            ;; Bytes >=128: leave as raw bytes (Lua 5.5 %q behavior)
            (>= (int c) 128)
            (.append result c)
            ;; Regular ASCII characters
            :else (.append result c))
          (recur (inc i)))))
    (.append result "\"")
    (str result)))

(defn- strip-g-zeros
  "Strip trailing zeros from a Java %g-formatted number string.
   Java's String.format does not strip trailing zeros for %g like C's printf."
  [^String s]
  (let [n (.length s)
        e-pos (loop [i 0]
                (cond (>= i n) nil
                      (let [c (.charAt s i)] (or (= c \e) (= c \E))) i
                      :else (recur (inc i))))
        strip (fn [^String m]
                (let [m2 (str/replace m #"0+$" "")]
                  (if (and (pos? (.length m2))
                           (not (Character/isDigit (.charAt m2 (dec (.length m2))))))
                    (subs m2 0 (dec (.length m2)))
                    m2)))]
    (if e-pos
      (str (strip (subs s 0 e-pos)) (subs s e-pos))
      (strip s))))

(defn- parse-format-spec
  "Parse a format specifier like %d, %5d, %05d, %-10s, etc.
   Returns [spec-end flags width precision type]"
  [fmt start]
  (let [len (long (count fmt))]
    (loop [j (unchecked-inc (long start))                   ;; Start after the %
           flags ""
           width nil
           precision nil]
      (if (>= j len)
        [j flags width precision nil]                       ;; No type found
        (let [ch (nth fmt j)]
          (cond
            ;; Flags: - + space 0 #
            ;; Allow multiple flags at the beginning (remove the position check)
            (and (nil? width) (nil? precision) (or (= ch \-) (= ch \+) (= ch \space) (= ch \0) (= ch \#)))
            (recur (unchecked-inc j) (str flags ch) width precision)

            ;; Width (digits)
            (and (nil? width) (Character/isDigit (int ch)))
            (let [width-end (long (loop [k j]
                                    (if (and (< k len) (Character/isDigit (int (nth fmt k))))
                                      (recur (unchecked-inc k))
                                      k)))
                  width-str (subs fmt j width-end)
                  parsed-width (try
                                 (Integer/parseInt width-str)
                                 (catch NumberFormatException _
                                   (throw (ex-info "too long" {:type :error}))))]
              (recur width-end flags parsed-width precision))

            ;; Precision (.digits)
            (and (= ch \.) (nil? precision))
            (let [prec-start (unchecked-inc j)
                  prec-end (long (loop [k prec-start]
                                   (if (and (< k len) (Character/isDigit (int (nth fmt k))))
                                     (recur (unchecked-inc k))
                                     k)))
                  prec-str (if (= prec-start prec-end) "0" (subs fmt prec-start prec-end))
                  parsed-prec (try
                                (Integer/parseInt prec-str)
                                (catch NumberFormatException _
                                  (throw (ex-info "too long" {:type :error}))))]
              (recur prec-end flags width parsed-prec))

            ;; Type specifier (letter)
            (Character/isLetter (int ch))
            [(unchecked-inc j) flags width precision ch]

            ;; Unknown character
            :else
            [j flags width precision nil]))))))

(defn lua-format
  "string.format(formatstring, ...) - Returns formatted string (printf-style)."
  [fmt & args]
  (loop [i 0
         arg-idx 0
         result (StringBuilder.)]
    (if (< i (count fmt))
      (let [c (nth fmt i)]
        (if (= c \%)
          (if (< (inc i) (count fmt))
            (let [next-c (nth fmt (inc i))]
              (cond
                ;; %% - literal %
                (= next-c \%)
                (do
                  (.append result \%)
                  (recur (+ i 2) arg-idx result))

                ;; %q - format for safe reading by Lua interpreter
                ;; Only works for: strings, numbers, booleans, nil
                ;; Tables/functions/etc should error
                (= next-c \q)
                (do
                  (let [arg (nth args arg-idx)]
                    (.append result
                             (cond
                               ;; Numbers: format without quotes
                               ;; Special float values use expressions so load() can reconstruct them
                               (number? arg)
                               (let [d (double arg)]
                                 (cond
                                   (Double/isNaN d) "(0/0)"
                                   (Double/isInfinite d) (if (pos? d) "(1/0)" "(-1/0)")
                                   :else (str arg)))
                               ;; Booleans: as-is
                               (or (= arg true) (= arg false)) (str arg)
                               ;; nil: as-is
                               (nil? arg) "nil"
                               ;; Strings: quote and escape
                               (string? arg) (quote-string arg)
                               ;; Everything else (tables, functions, etc): error
                               :else (throw (ex-info "no literal representation"
                                                     {:type :format-error
                                                      :value arg})))))
                  (recur (+ i 2) (inc arg-idx) result))

                ;; Other format specifiers
                :else
                (let [[spec-end flags width precision type] (parse-format-spec fmt i)
                      spec-end (long spec-end)
                      width (when width (long width))
                      precision (when precision (long precision))]
                  ;; Check that the raw format spec is not too long (Lua limit: 200)
                  (when (> (unchecked-subtract spec-end i) 200)
                    (throw (ex-info "too long" {:type :error})))
                  ;; Validation checks
                  (when (or (nil? type)
                            (not (some #(= type %) [\c \d \i \o \u \x \X \f \e \E \g \G \a \A \s \p \q])))
                    (throw (ex-info "invalid conversion" {:type :error})))
                  ;; %q cannot have any modifiers (flags/width/precision)
                  (when (= type \q)
                    (throw (ex-info "cannot have modifiers" {:type :error})))
                  (when (> (count flags) 5)
                    (throw (ex-info "repeated flags" {:type :error})))
                  ;; Width/precision > 99 is invalid per Lua spec
                  (when (and width (> (long width) 99))
                    (throw (ex-info "invalid conversion" {:type :error})))
                  (when (and precision (> (long precision) 99))
                    (throw (ex-info "invalid conversion" {:type :error})))
                  ;; Invalid flag/modifier combinations
                  (when (and (= type \c) (or (str/includes? flags "0") (some? precision)))
                    (throw (ex-info "invalid conversion" {:type :error})))
                  (when (and (= type \s) (str/includes? flags "0"))
                    (throw (ex-info "invalid conversion" {:type :error})))
                  (when (and (contains? #{\d \i} type) (str/includes? flags "#"))
                    (throw (ex-info "invalid conversion" {:type :error})))
                  (when (and (= type \p) (some? precision))
                    (throw (ex-info "invalid conversion" {:type :error})))
                  (when (>= arg-idx (count args))
                    (throw (ex-info "no value" {:type :error})))
                  (let [arg (nth args arg-idx nil)
                        formatted (case type
                                    \c                      ;; Character from number
                                    (let [ch-str (str (char (int arg)))
                                          left-align (str/includes? flags "-")
                                          target-width (long (or width 0))
                                          padded (if (< (count ch-str) target-width)
                                                   (let [padding (apply str (repeat (unchecked-subtract target-width (long (count ch-str))) \space))]
                                                     (if left-align
                                                       (str ch-str padding)
                                                       (str padding ch-str)))
                                                   ch-str)]
                                      padded)

                                    (\d \i)                 ;; Decimal integer
                                    (let [num (long arg)
                                          negative? (< num 0)
                                          ;; Handle Long/MIN_VALUE overflow: Math/abs(Long/MIN_VALUE) = Long/MIN_VALUE
                                          raw-abs (if (= num Long/MIN_VALUE)
                                                    "9223372036854775808"
                                                    (str (Math/abs num)))
                                          ;; Apply precision: minimum digits (precision 0 + zero value = empty)
                                          abs-str (cond
                                                    (and precision (= (long precision) 0) (= num 0)) ""
                                                    (and precision (< (long (count raw-abs)) (long precision)))
                                                    (str (apply str (repeat (unchecked-subtract (long precision) (long (count raw-abs))) \0)) raw-abs)
                                                    :else raw-abs)
                                          ;; Determine sign prefix
                                          sign-prefix (cond
                                                        negative? "-"
                                                        (str/includes? flags "+") "+"
                                                        (str/includes? flags " ") " "
                                                        :else "")
                                          num-str (str sign-prefix abs-str)
                                          ;; Precision disables zero-padding flag
                                          pad-char (if (and (str/includes? flags "0") (nil? precision)) \0 \space)
                                          left-align (str/includes? flags "-")
                                          target-width (long (or width 0))
                                          ;; With zero-padding, sign goes before zeros
                                          padded (if (< (count num-str) target-width)
                                                   (let [pad-amount (unchecked-subtract target-width (long (count num-str)))]
                                                     (if left-align
                                                       ;; Left align: number then spaces
                                                       (str num-str (apply str (repeat pad-amount \space)))
                                                       ;; Right align with zero-padding: sign, zeros, number
                                                       (if (= pad-char \0)
                                                         (str sign-prefix (apply str (repeat pad-amount \0)) abs-str)
                                                         ;; Right align with space-padding: spaces, full number
                                                         (str (apply str (repeat pad-amount \space)) num-str))))
                                                   num-str)]
                                      padded)

                                    (\x \X)                 ;; Hexadecimal
                                    (let [hex-str (Long/toHexString (long arg))
                                          hex-str (if (= type \X) (str/upper-case hex-str) hex-str)
                                          ;; Add 0x/0X prefix if # flag is present
                                          with-prefix (if (str/includes? flags "#")
                                                        (str (if (= type \X) "0X" "0x") hex-str)
                                                        hex-str)
                                          ;; Apply width and padding
                                          pad-char (if (str/includes? flags "0") \0 \space)
                                          left-align (str/includes? flags "-")
                                          target-width (long (or width 0))
                                          padded (if (< (count with-prefix) target-width)
                                                   (let [padding (apply str (repeat (unchecked-subtract target-width (long (count with-prefix))) pad-char))]
                                                     (if left-align
                                                       (str with-prefix padding)
                                                       (str padding with-prefix)))
                                                   with-prefix)]
                                      padded)

                                    \o                      ;; Octal
                                    (let [oct-str (Long/toOctalString (long arg))
                                          ;; Add 0 prefix if # flag is present
                                          with-prefix (if (str/includes? flags "#")
                                                        (str "0" oct-str)
                                                        oct-str)
                                          ;; Apply width and padding
                                          pad-char (if (str/includes? flags "0") \0 \space)
                                          left-align (str/includes? flags "-")
                                          target-width (long (or width 0))
                                          padded (if (< (count with-prefix) target-width)
                                                   (let [padding (apply str (repeat (unchecked-subtract target-width (long (count with-prefix))) pad-char))]
                                                     (if left-align
                                                       (str with-prefix padding)
                                                       (str padding with-prefix)))
                                                   with-prefix)]
                                      padded)

                                    \u                      ;; Unsigned integer
                                    (let [num (long arg)
                                          ;; Convert to unsigned representation
                                          ;; For negative numbers, interpret as unsigned 64-bit
                                          unsigned (if (< num 0)
                                                     (.add (BigInteger/valueOf num)
                                                           (.shiftLeft BigInteger/ONE 64))
                                                     num)
                                          raw-str (str unsigned)
                                          ;; Apply precision: minimum digits (precision 0 + zero value = empty)
                                          num-str (cond
                                                    (and precision (= (long precision) 0) (= unsigned 0)) ""
                                                    (and precision (< (long (count raw-str)) (long precision)))
                                                    (str (apply str (repeat (unchecked-subtract (long precision) (long (count raw-str))) \0)) raw-str)
                                                    :else raw-str)
                                          ;; Apply width and padding (no sign handling for unsigned)
                                          pad-char (if (and (str/includes? flags "0") (nil? precision)) \0 \space)
                                          left-align (str/includes? flags "-")
                                          target-width (long (or width 0))
                                          padded (if (< (count num-str) target-width)
                                                   (let [padding (apply str (repeat (unchecked-subtract target-width (long (count num-str))) pad-char))]
                                                     (if left-align
                                                       (str num-str padding)
                                                       (str padding num-str)))
                                                   num-str)]
                                      padded)

                                    \f                      ;; Float decimal
                                    (let [prec (long (or precision 6))
                                          num (double arg)
                                          loc (env/get-numeric-locale env/*current-env*)
                                          java-flags (str/replace flags "#" "")
                                          ;; With # flag and precision 0, Java won't produce a decimal
                                          ;; point naturally, so we add it manually. Subtract 1 from
                                          ;; width so the appended dot doesn't exceed the total width.
                                          need-dot (and (str/includes? flags "#") (zero? prec))
                                          adj-width (when width (if need-dot (unchecked-dec (long width)) (long width)))
                                          java-fmt (str "%" java-flags
                                                        (when adj-width adj-width) "." prec "f")
                                          raw (String/format loc java-fmt (into-array Object [num]))
                                          result (if need-dot (str raw ".") raw)]
                                      result)

                                    (\e \E)                 ;; Float scientific notation
                                    (let [prec (long (or precision 6))
                                          num (double arg)
                                          loc (env/get-numeric-locale env/*current-env*)
                                          java-flags (str/replace flags "#" "")
                                          java-fmt (str "%" java-flags
                                                        (when width width) "." prec
                                                        (if (= type \e) "e" "E"))]
                                      (String/format loc java-fmt (into-array Object [num])))

                                    (\g \G)                 ;; Float general (shorter of %f / %e)
                                    (let [prec (long (or precision 6))
                                          num (double arg)
                                          loc (env/get-numeric-locale env/*current-env*)
                                          ;; Pass flags/width through to Java, except # needs special handling
                                          has-hash (str/includes? flags "#")
                                          java-flags (str/replace flags "#" "")
                                          java-fmt (str "%" java-flags
                                                        (when width width) "." prec
                                                        (if (= type \g) "g" "G"))
                                          raw (String/format loc java-fmt (into-array Object [num]))]
                                      (if has-hash raw (strip-g-zeros raw)))

                                    (\a \A)                 ;; Hexadecimal float
                                    (let [num (double arg)
                                          is-upper (= type \A)
                                          negative? (< num 0)]
                                      (cond
                                        (Double/isInfinite num)
                                        (if negative?
                                          (if is-upper "-INF" "-inf")
                                          (if is-upper "INF" "inf"))
                                        (Double/isNaN num)
                                        (if is-upper "NAN" "nan")
                                        :else
                                        ;; Use Java's hex float format and handle precision
                                        (let [hex-str (Double/toHexString num)
                                              ;; Parse hex format: [sign]0x1.234p5
                                              ;; Apply precision to fractional part if specified
                                              adjusted (if precision
                                                         (if-let [[_ sign-part int-part frac-part exp-part]
                                                                  (re-matches #"([+-]?)0x([0-9a-f])\.?([0-9a-f]*)p([+-]?\d+)" hex-str)]
                                                           (let [;; Pad or truncate fractional part to precision
                                                                 padded-frac (if (< (long (count frac-part)) (long precision))
                                                                               (str frac-part (apply str (repeat (unchecked-subtract (long precision) (long (count frac-part))) "0")))
                                                                               (subs frac-part 0 (int (long precision))))
                                                                 ;; Reconstruct with precision
                                                                 result-str (str sign-part "0x" int-part "." padded-frac "p" exp-part)]
                                                             result-str)
                                                           hex-str) ;; Pattern didn't match, return as-is
                                                         hex-str)
                                              ;; Add sign prefix for positive numbers if + flag
                                              with-sign (if (and (not negative?) (str/includes? flags "+"))
                                                          (str "+" adjusted)
                                                          adjusted)
                                              result (if is-upper (str/upper-case with-sign) with-sign)]
                                          result)))

                                    \s                      ;; String
                                    (let [s (cond
                                              (nil? arg) "nil"
                                              (true? arg) "true"
                                              (false? arg) "false"
                                              ;; For tables, respect __tostring and __name metamethods
                                              (interp/lua-table? arg)
                                              (if-let [tostring-mm (interp/get-metamethod arg "__tostring")]
                                                (let [result (interp/call-function tostring-mm [arg] env/*current-env*)
                                                      result-val (if (vector? result) (first result) result)]
                                                  (when-not (string? result-val)
                                                    (throw (ex-info "'__tostring' must return a string"
                                                                    {:type :error})))
                                                  (str result-val))
                                                ;; No __tostring, check for __name
                                                (if-let [mt (interp/get-metatable arg)]
                                                  (if-let [name (interp/table-get mt "__name")]
                                                    (str name ": " (format "%x" (System/identityHashCode arg)))
                                                    (str "table: " (format "%x" (System/identityHashCode arg))))
                                                  (str "table: " (format "%x" (System/identityHashCode arg)))))
                                              :else (str arg))]
                                      ;; Check for null bytes with width/precision (Lua restriction)
                                      ;; Null bytes are only forbidden in %s when width or precision is specified
                                      (when (and (or width precision) (str/includes? s "\0"))
                                        (throw (ex-info "string contains zeros" {:type :error})))
                                      (let [;; Apply precision (max length) before padding
                                            s-truncated (if precision
                                                          (subs s 0 (int (Math/min (long (count s)) (long precision))))
                                                          s)
                                            left-align (str/includes? flags "-")
                                            target-width (long (or width 0))
                                            padded (if (< (count s-truncated) target-width)
                                                     (let [padding (apply str (repeat (unchecked-subtract target-width (long (count s-truncated))) \space))]
                                                       (if left-align
                                                         (str s-truncated padding)
                                                         (str padding s-truncated)))
                                                     s-truncated)]
                                        padded))

                                    \p                      ;; Pointer address (Lua 5.4)
                                    (let [ptr-str (cond
                                                    (or (nil? arg) (boolean? arg) (number? arg))
                                                    "(null)"
                                                    ;; Short strings: content-based stable ID.
                                                    ;; Lua interns short strings globally so equal
                                                    ;; short strings always have the same %p address.
                                                    (and (string? arg) (< (count arg) 40))
                                                    (str "0x" (Long/toHexString (short-str-ptr arg)))
                                                    ;; Long strings / tables / functions: object identity.
                                                    :else
                                                    (str "0x" (Long/toHexString (System/identityHashCode arg))))
                                          left-align (str/includes? flags "-")
                                          target-width (long (or width 0))
                                          padded (if (< (count ptr-str) target-width)
                                                   (let [padding (apply str (repeat (unchecked-subtract target-width (long (count ptr-str))) \space))]
                                                     (if left-align
                                                       (str ptr-str padding)
                                                       (str padding ptr-str)))
                                                   ptr-str)]
                                      padded)

                                    ;; Unknown type - just return the arg as string
                                    (str arg))]
                    (.append result formatted)
                    (recur spec-end (inc arg-idx) result)))))
            ;; % at end of string
            (do
              (.append result \%)
              (recur (inc i) arg-idx result)))
          ;; Regular character
          (do
            (.append result c)
            (recur (inc i) arg-idx result))))
      (str result))))

(defn lua-find
  "string.find(s, pattern [, init [, plain]]) - Find pattern in s.
   Returns start, end indices (1-based) and any captures, or nil if not found.
   If plain is true, pattern is a plain string (no pattern matching)."
  [s pattern & [init plain]]
  (let [s (check-string-coerce s 1 "find")
        pattern (str pattern)
        len (long (count s))
        raw-init (unchecked-dec (long (or init 1)))
        init (long (if (neg? raw-init)
                     (max 0 (unchecked-add len (unchecked-add raw-init 1)))
                     raw-init))]
    (when (<= init len)
      (if plain
        (let [idx (.indexOf ^String s ^String pattern (int init))]
          (when (>= idx 0)
            [(unchecked-inc idx) (unchecked-add idx (long (count pattern)))]))
        (when-let [{:keys [start end caps]} (lua-pattern-find s pattern init)]
          (let [start (long start)
                end (long end)
                cap-vals (extract-cap-values s caps)]
            (if (seq cap-vals)
              (vec (concat [(unchecked-inc start) end] cap-vals))
              [(unchecked-inc start) end])))))))

(defn lua-match
  "string.match(s, pattern [, init]) - Find first match of pattern in s.
   Returns captures if pattern has them, otherwise the whole match."
  [s pattern & [init]]
  (let [s (str s)
        pattern (str pattern)
        len (long (count s))
        raw-init (unchecked-dec (long (or init 1)))
        init (long (if (neg? raw-init)
                     (max 0 (unchecked-add len (unchecked-add raw-init 1)))
                     raw-init))]
    (when-let [{:keys [start end caps]} (lua-pattern-find s pattern init)]
      (let [start (long start)
            end (long end)
            cap-vals (extract-cap-values s caps)]
        (if (seq cap-vals)
          (if (= 1 (count cap-vals))
            (first cap-vals)
            (vec cap-vals))
          (subs s start end))))))

(defn lua-gmatch
  "string.gmatch(s, pattern [, init]) - Returns an iterator function that yields successive matches.
   Implements Lua 5.3.3 empty-match semantics: after a non-empty match, an empty match
   at the same position is skipped (not yielded), and the iterator tries from the next
   position. This prevents infinite loops and matches PUC-Lua 5.3.3+ behavior.

   The optional init argument (added in Lua 5.4) specifies the starting position (1-based).
   Negative values count from the end of the string."
  ([s pattern] (lua-gmatch s pattern nil))
  ([s pattern init]
   (let [s (str s)
         slen (long (count s))
         start-pos (long (if (nil? init)
                           0
                           (let [i (long init)]
                             (if (neg? i)
                               (max 0 (unchecked-add slen i))
                               (max 0 (unchecked-dec i))))))
         pos (atom start-pos)
         after-nonempty (atom false)]
     (with-meta (fn [& _args]
       (loop []
         (let [try-pos (long @pos)]
           (when (<= try-pos slen)
             (let [result (lua-pattern-find s pattern try-pos)]
               (if result
                 (let [{:keys [start end caps]} result
                       start (long start)
                       end (long end)
                       empty? (= start end)]
                   (if (and empty? @after-nonempty)
                     (do (reset! after-nonempty false)
                         (reset! pos (unchecked-inc try-pos))
                         (recur))
                     (do (reset! after-nonempty (not empty?))
                         (reset! pos (if empty? (unchecked-inc end) end))
                         (let [cap-vals (extract-cap-values s caps)]
                           (if (seq cap-vals)
                             (if (= 1 (count cap-vals))
                               (first cap-vals)
                               (vec cap-vals))
                             (subs s start end))))))
                 nil)))))) {:clua/nups 1}))))

(defn- gsub-replacement
  "Compute the replacement text for a gsub match.
   Returns [text changed?] where changed? is false when the replacement was
   nil/false (fn or table lookup) — matching Lua 5.5's 'changed' flag so that
   gsub can return the original string object when no actual substitution occurs.

   String replacement rules (PUC-Lua compatible):
   - %0  → whole match
   - %1  → capture 1, or whole match if no captures (PUC-Lua special case)
   - %N  (N≥2, no captures) → error 'invalid capture index %N'
   - %N  (N > capture count) → error 'invalid capture index %N'
   - %%  → literal %
   - %x  (other) → error 'invalid use of %'"
  [repl match captures _matcher]
  (cond
    (string? repl)
    (let [cap-count (long (if captures (count captures) 0))
          sb (StringBuilder.)
          n (long (count repl))]
      (loop [i (long 0)]
        (if (>= i n)
          [(str sb) true]
          (let [c (.charAt ^String repl (int i))]
            (if (not= c \%)
              (do (.append sb c) (recur (unchecked-inc i)))
              (if (>= (unchecked-inc i) n)
                ;; Trailing % with no following char: keep as-is
                (do (.append sb c) (recur (unchecked-inc i)))
                (let [nc (.charAt ^String repl (int (unchecked-inc i)))]
                  (cond
                    (= nc \%)
                    (do (.append sb \%) (recur (unchecked-add i 2)))
                    (Character/isDigit ^char nc)
                    (let [idx (long (Character/digit ^char nc 10))]
                      (cond
                        (zero? idx)
                        (do (.append sb match) (recur (unchecked-add i 2)))
                        (and (= idx 1) (zero? cap-count))
                        ;; %1 with no captures = whole match (PUC-Lua compat)
                        (do (.append sb match) (recur (unchecked-add i 2)))
                        (> idx cap-count)
                        (throw (ex-info (str "invalid capture index %" idx)
                                        {:type :error}))
                        :else
                        (do (.append sb (str (nth captures (int (unchecked-dec idx)))))
                            (recur (unchecked-add i 2)))))
                    :else
                    (throw (ex-info "invalid use of '%'" {:type :error}))))))))))

    (or (fn? repl)
        (and (map? repl) (= :lua-function (:type repl))))
    (let [groups (or captures [match])
          raw (binding [coro/*unyieldable-depth* (unchecked-inc (long coro/*unyieldable-depth*))]
                (interp/call-function repl groups env/*current-env*))
          res (if (vector? raw) (first raw) raw)]
      (cond (nil? res) [match false] (false? res) [match false] :else [(str res) true]))

    (and (map? repl) (= :lua-table (:type repl)))
    (let [key (if captures (first captures) match)
          val (tables/table-get-with-meta repl key env/*current-env*)]
      (cond
        (or (nil? val) (false? val)) [match false]
        (and (map? val) (= :lua-table (:type val)))
        (throw (ex-info "invalid replacement value (a table)" {:type :error}))
        :else [(str val) true]))

    :else [(str repl) true]))

(defn lua-gsub
  "string.gsub(s, pattern, repl [, n]) - Replace pattern in s with repl.
   repl can be a string, table, or function. Returns new string and count.

   Implements Lua 5.3.3 empty-match semantics: after a non-empty match ending
   at position E, an empty match at E is skipped (the char at E is copied to
   output as-is). This prevents double replacements at boundaries."
  [s pattern repl & [n]]
  (let [s (str s)
        pattern (str pattern)
        n (long (or n Integer/MAX_VALUE))
        slen (long (count s))
        result (StringBuilder.)
        cnt (atom (long 0))
        changed? (atom false)]
    (loop [last-end (long 0)
           after-nonempty false]
      (if (< (long @cnt) n)
        (let [result-map (lua-pattern-find s pattern last-end)]
          (if result-map
            (let [{:keys [start end caps]} result-map
                  start (long start)
                  end (long end)
                  empty? (= start end)]
              (if (and empty? after-nonempty (= start last-end))
                ;; Skip empty match right after non-empty: copy char at start and advance
                (do (.append result (subs s last-end (int (Math/min (unchecked-inc start) slen))))
                    (recur (Math/min (unchecked-inc start) slen) false))
                ;; Process this match normally
                (let [match (subs s start end)
                      cap-vals (extract-cap-values s caps)
                      captures (when (seq cap-vals) (vec cap-vals))
                      [repl-text ch] (gsub-replacement repl match captures nil)]
                  (.append result (subs s last-end start))
                  (.append result repl-text)
                  (when ch (reset! changed? true))
                  (swap! cnt (fn [^long x] (unchecked-inc x)))
                  (if empty?
                    ;; Empty match: copy char at start (if within string) and advance
                    (if (< start slen)
                      (do (.append result (subs s start (int (unchecked-inc start))))
                          (recur (unchecked-inc start) false))
                      ;; Empty match at end of string: done
                      (do (.append result (subs s end))
                          [(if @changed? (str result) s) @cnt]))
                    ;; Non-empty match
                    (recur end true)))))
            ;; No more matches: append remaining string
            (do (.append result (subs s last-end))
                [(if @changed? (str result) s) @cnt])))
        ;; Reached replacement limit
        (do (.append result (subs s last-end))
            [(if @changed? (str result) s) @cnt])))))

;; =============================================================================
;; Binary Packing Functions — Lua 5.3 compliant
;; =============================================================================

;; --- helpers ----------------------------------------------------------------

(defn- ^:private power-of-2? [^long n]
  (and (pos? n) (zero? (bit-and n (unchecked-dec n)))))

(defn- ^:private pack-error [msg]
  (throw (ex-info msg {:type :error})))

(defn- ^:private read-opt-int
  "Read optional decimal integer after current position in fmt string.
   Returns [value, chars-consumed]. If no digit, returns [default, 0].
   Throws on numeric overflow."
  [^String fmt ^long start default]
  (let [len (count fmt)]
    (if (or (>= start len) (not (Character/isDigit (.charAt fmt (int start)))))
      [default 0]
      (loop [i start acc (long 0)]
        (if (or (>= i len) (not (Character/isDigit (.charAt fmt (int i)))))
          [acc (- i start)]
          (let [d (long (- (int (.charAt fmt (int i))) (int \0)))]
            ;; Overflow-safe: acc*10 + d <= Long/MAX_VALUE iff acc <= (MAX-d)/10
            (when (> acc (quot (- Long/MAX_VALUE d) 10))
              (pack-error (str "invalid format")))
            (recur (inc i) (+ (* acc 10) d))))))))

(defn- ^:private parse-format
  "Parse a Lua 5.3 pack format string into a vector of directive maps.
   State: endian (:little/:big/:native), max-align (int, default 1).
   Native endian is little-endian on JVM (matching x86)."
  [^String fmt & {:keys [reject-variable] :or {reject-variable false}}]
  (let [native-endian :little                               ;; JVM on x86/x64
        len (count fmt)]
    (loop [i 0
           endian native-endian
           max-align (int 1)
           directives []]
      (if (>= i len)
        directives
        (let [c (.charAt fmt (int i))]
          (case c
            ;; endianness / alignment controls
            \< (recur (inc i) :little max-align directives)
            \> (recur (inc i) :big max-align directives)
            \= (recur (inc i) native-endian max-align directives)

            \! (let [[n consumed] (read-opt-int fmt (inc i) 0) ;; default = native align
                     ma (long (if (zero? (long consumed)) 8 (long n)))] ;; !  => native max (8 on 64-bit)
                 (when (or (< ma 1) (> ma 16))
                   (pack-error (str "(" ma ") out of limits [1,16]")))
                 (when-not (power-of-2? ma)
                   (pack-error (str "not power of 2")))
                 (recur (unchecked-add (unchecked-inc i) (long consumed)) endian ma directives))

            \space (recur (inc i) endian max-align directives)

            ;; integer formats
            (\b \B \h \H \l \L \j \J \T
              \i \I \f \d \n
              \c \s \z \x \X)
            (let [signed? (case c (\b \h \l \j \i) true false)
                  [op size natural consumed]
                  (case c
                    \b [:int 1 1 0]
                    \B [:uint 1 1 0]
                    \h [:int 2 2 0]
                    \H [:uint 2 2 0]
                    \l [:int 4 4 0]                         ;; JVM native long = 4 bytes in Lua sense
                    \L [:uint 4 4 0]
                    \j [:int 8 8 0]
                    \J [:uint 8 8 0]
                    \T [:uint 8 8 0]                        ;; size_t = 8 on 64-bit
                    \i (let [[n nc] (read-opt-int fmt (inc i) 4)]
                         [:int n n nc])
                    \I (let [[n nc] (read-opt-int fmt (inc i) 4)]
                         [:uint n n nc])
                    \f [:float 4 4 0]
                    \d [:double 8 8 0]
                    \n [:double 8 8 0]                      ;; Lua number = double
                    \c (let [[n nc] (read-opt-int fmt (inc i) -1)]
                         (when (= n -1)
                           (pack-error "missing size"))
                         [:fixed-str n 0 nc])
                    \s (let [[n nc] (read-opt-int fmt (inc i) 8)]
                         (when reject-variable
                           (pack-error "variable-length format"))
                         [:len-str n n nc])
                    \z (do (when reject-variable
                             (pack-error "variable-length format"))
                           [:zstr 0 0 0])
                    \x [:pad-byte 1 0 0]
                    \X (let [ni (inc i)]
                         (when (>= ni len)
                           (pack-error "invalid next option for option 'X'"))
                         (let [nc (.charAt fmt (int ni))
                               [xalign inner-digits]
                               (case nc
                                 \b [1 0] \B [1 0]
                                 \h [2 0] \H [2 0]
                                 \l [4 0] \L [4 0]
                                 \j [8 0] \J [8 0] \T [8 0]
                                 \i (let [[n nc2] (read-opt-int fmt (+ ni 1) 4)
                                          n (long n)]
                                      (when (or (< n 1) (> n 16))
                                        (pack-error (str "(" n ") out of limits [1,16]")))
                                      [n nc2])
                                 \I (let [[n nc2] (read-opt-int fmt (+ ni 1) 4)
                                          n (long n)]
                                      (when (or (< n 1) (> n 16))
                                        (pack-error (str "(" n ") out of limits [1,16]")))
                                      [n nc2])
                                 \f [4 0]
                                 \d [8 0]
                                 \n [8 0]
                                 ;; anything else (including x, c, s, z, space) is invalid for X
                                 [nil 0])]
                           (when (or (nil? xalign) (zero? (long xalign)))
                             (pack-error "invalid next option for option 'X'"))
                           [:align-only 0 xalign (unchecked-add 1 (long inner-digits))]))) ;; +1 for the inner op char
                  size (long size)
                  natural (long natural)
                  consumed (long consumed)
                  ;; Validate size for integer types
                  _ (when (#{:int :uint} op)
                      (when (or (< size 1) (> size 16))
                        (pack-error (str "(" size ") out of limits [1,16]"))))
                  ;; Validate size for len-str prefix
                  _ (when (= op :len-str)
                      (when (or (< size 1) (> size 16))
                        (pack-error (str "(" size ") out of limits [1,16]"))))
                  actual-align (long (if (zero? natural)
                                       0
                                       (Math/min natural (long max-align))))
                  _ (when (and (pos? actual-align) (not (power-of-2? actual-align)))
                      (pack-error "not power of 2"))
                  directive {:op op :size size :endian endian
                             :max-align max-align :natural-align natural
                             :actual-align (if (zero? natural) 0 actual-align)
                             :signed? signed?}]
              (recur (unchecked-add (unchecked-inc i) consumed) endian max-align (conj directives directive)))

            ;; unknown format character
            (pack-error (str "invalid format option '" c "'"))))))))

;; --- byte I/O helpers -------------------------------------------------------

(defn- ^:private align-padding
  "Compute padding bytes needed to align pos to actual-align."
  [^long pos ^long actual-align]
  (if (<= actual-align 1)
    0
    (let [r (long (mod pos actual-align))]
      (if (zero? r) 0 (unchecked-subtract actual-align r)))))

(defn- ^:private write-int-bytes
  "Write n bytes from a long value into byte-array buf starting at offset.
   endian :little or :big. For n > 8, extends with sign-byte (0x00 or 0xFF)."
  [^bytes buf offset value n endian _signed?]
  (let [offset (long offset)
        value (long value)
        n (long n)
        sign-byte (if (neg? value) (unchecked-byte 0xFF) (unchecked-byte 0x00))]
    (if (= endian :little)
      (do
        ;; Low bytes from value
        (loop [k (long 0) v value]
          (when (< k (Math/min n 8))
            (aset buf (int (unchecked-add offset k)) (unchecked-byte (bit-and v 0xFF)))
            (recur (unchecked-inc k) (unsigned-bit-shift-right v 8))))
        ;; Extension bytes for n > 8
        (loop [k (long 8)]
          (when (< k n)
            (aset buf (int (unchecked-add offset k)) sign-byte)
            (recur (unchecked-inc k)))))
      ;; big endian
      (do
        ;; Extension bytes at the front for n > 8
        (loop [k (long 0)]
          (when (< k (unchecked-subtract n 8))
            (aset buf (int (unchecked-add offset k)) sign-byte)
            (recur (unchecked-inc k))))
        ;; Value bytes (big-endian, last min(n,8) bytes)
        (let [start (long (Math/max 0 (unchecked-subtract n 8)))
              nbytes (long (Math/min n 8))]
          (loop [k (unchecked-dec nbytes) v value]
            (when (>= k 0)
              (aset buf (int (unchecked-add offset (unchecked-add start k))) (unchecked-byte (bit-and v 0xFF)))
              (recur (unchecked-dec k) (unsigned-bit-shift-right v 8)))))))))

(defn- ^:private sign-extend
  "Sign-extend an n-byte unsigned value to a 64-bit signed long."
  [^long value ^long n]
  (if (< n 8)
    (let [sign-bit (bit-and value (bit-shift-left 1 (dec (* n 8))))]
      (if (pos? sign-bit)
        ;; High bit is set, extend sign
        (bit-or value (bit-shift-left -1 (* n 8)))
        value))
    value))

(defn- ^:private read-int-bytes
  "Read n bytes from byte-array buf starting at offset, return a long.
   For n > 8, validates that extra bytes are valid sign/zero extension."
  [^bytes buf offset n endian signed?]
  (let [offset (long offset)
        n (long n)]
    (if (= endian :little)
      (let [;; Read low min(n,8) bytes into long
            nbytes (long (Math/min n 8))
            raw-value (loop [k (unchecked-dec nbytes) acc (long 0)]
                        (if (< k 0)
                          acc
                          (let [b (bit-and (long (aget buf (int (unchecked-add offset k)))) 0xFF)]
                            (recur (unchecked-dec k) (bit-or (bit-shift-left acc 8) b)))))
            ;; For n > 8, check extension bytes
            _ (when (> n 8)
                (let [sign-bit (bit-and (long (aget buf (int (unchecked-add offset 7)))) 0x80)
                      ext-expected (if signed?
                                     (if (pos? sign-bit) 0xFF 0x00)
                                     ;; unsigned: extra bytes should be 0 for values that fit
                                     ;; but we also accept 0xFF if the value itself has high bit (wrapping)
                                     0x00)]
                  (loop [k (long 8)]
                    (when (< k n)
                      (let [b (bit-and (long (aget buf (int (unchecked-add offset k)))) 0xFF)]
                        (when (not= b ext-expected)
                          (pack-error (str n "-byte integer does not fit into Lua Integer")))
                        (recur (unchecked-inc k)))))))]
        ;; Apply sign extension for signed types with n <= 8
        (if signed?
          (sign-extend raw-value (long (Math/min n 8)))
          raw-value))
      ;; big endian
      (let [extra (long (Math/max 0 (unchecked-subtract n 8)))
            ;; Check extension bytes at front
            _ (when (> n 8)
                (let [first-value-byte (bit-and (long (aget buf (int (unchecked-add offset extra)))) 0xFF)
                      sign-bit (bit-and first-value-byte 0x80)
                      ext-expected (if signed?
                                     (if (pos? sign-bit) 0xFF 0x00)
                                     0x00)]
                  (loop [k (long 0)]
                    (when (< k extra)
                      (let [b (bit-and (long (aget buf (int (unchecked-add offset k)))) 0xFF)]
                        (when (not= b ext-expected)
                          (pack-error (str n "-byte integer does not fit into Lua Integer")))
                        (recur (unchecked-inc k)))))))
            ;; Read min(n,8) value bytes
            nbytes (long (Math/min n 8))
            raw-value (loop [k (long 0) acc (long 0)]
                        (if (>= k nbytes)
                          acc
                          (let [b (bit-and (long (aget buf (int (unchecked-add offset (unchecked-add extra k))))) 0xFF)]
                            (recur (unchecked-inc k) (bit-or (bit-shift-left acc 8) b)))))]
        (if signed?
          (sign-extend raw-value (long (Math/min n 8)))
          raw-value)))))

(defn- ^:private check-pack-range
  "Check that value fits in n bytes for signed/unsigned packing."
  [^long value ^long n signed?]
  (when (<= n 7)                                            ;; For n >= 8, any long fits
    (if signed?
      (let [min-val (- (bit-shift-left 1 (dec (* n 8))))
            max-val (dec (bit-shift-left 1 (dec (* n 8))))]
        (when (or (< value min-val) (> value max-val))
          (pack-error (str "integer overflow"))))
      ;; unsigned
      (let [umax (if (>= (* n 8) 64)
                   -1                                       ;; all bits set
                   (dec (bit-shift-left 1 (* n 8))))]
        (when (or (and (neg? value) (> n 7))
                  (neg? value)
                  (and (< (* n 8) 64) (> value umax)))
          (pack-error (str "unsigned integer overflow")))))))

(defn- ^:private write-float-bytes
  "Write a float (4 bytes) into buf at offset with given endian."
  [^bytes buf ^long offset ^double value endian]
  (let [bb (ByteBuffer/allocate 4)]
    (.order bb (if (= endian :little) ByteOrder/LITTLE_ENDIAN ByteOrder/BIG_ENDIAN))
    (.putFloat bb (Float. value))
    (System/arraycopy (.array bb) 0 buf (int offset) 4)))

(defn- ^:private write-double-bytes
  "Write a double (8 bytes) into buf at offset with given endian."
  [^bytes buf ^long offset ^double value endian]
  (let [bb (ByteBuffer/allocate 8)]
    (.order bb (if (= endian :little) ByteOrder/LITTLE_ENDIAN ByteOrder/BIG_ENDIAN))
    (.putDouble bb value)
    (System/arraycopy (.array bb) 0 buf offset 8)))

(defn- ^:private read-float-bytes
  "Read a float (4 bytes) from buf at offset with given endian."
  [^bytes buf ^long offset endian]
  (let [bb (ByteBuffer/wrap buf offset 4)]
    (.order bb (if (= endian :little) ByteOrder/LITTLE_ENDIAN ByteOrder/BIG_ENDIAN))
    (double (.getFloat bb))))

(defn- ^:private read-double-bytes
  "Read a double (8 bytes) from buf at offset with given endian."
  [^bytes buf ^long offset endian]
  (let [bb (ByteBuffer/wrap buf offset 8)]
    (.order bb (if (= endian :little) ByteOrder/LITTLE_ENDIAN ByteOrder/BIG_ENDIAN))
    (.getDouble bb)))

(defn- ^:private str->bytes
  "Convert a Lua string (ISO-8859-1) to byte array."
  ^bytes [^String s]
  (.getBytes s "ISO-8859-1"))

(defn- ^:private bytes->str
  "Convert byte array region to a Lua string (ISO-8859-1)."
  ^String [^bytes buf ^long offset ^long len]
  (String. buf (int offset) (int len) "ISO-8859-1"))

;; --- pack -------------------------------------------------------------------

(defn lua-pack
  "string.pack(fmt, v1, v2, ...) - Pack values into binary string.
   Full Lua 5.3 implementation."
  [fmt & values]
  (let [fmt (str fmt)
        directives (parse-format fmt)
        values (vec values)
        ;; Pre-calculate total size upper bound (generous)
        init-size (+ 256 (* 16 (count directives)))
        buf (byte-array init-size)
        ;; We'll use a resizable approach
        ]
    (loop [di (long 0)                                      ;; directive index
           vi (long 0)                                      ;; value index
           pos (long 0)                                     ;; current byte position
           out-buf buf]
      (if (>= di (count directives))
        (bytes->str out-buf 0 pos)
        (let [{:keys [op size endian actual-align signed?]} (nth directives di)
              size (long size)
              actual-align (long actual-align)
              ;; Apply alignment padding
              pad (long (align-padding pos (long (Math/max 1 actual-align))))
              _ (when (> pad (unchecked-subtract Long/MAX_VALUE pos))
                  (pack-error "format result too long"))
              pos (unchecked-add pos pad)
              ;; Ensure buffer is big enough
              added (long (case op
                            :fixed-str size
                            :len-str (unchecked-add size (long (if (< vi (count values))
                                                                 (count (str (nth values vi)))
                                                                 0)))
                            :zstr (long (if (< vi (count values))
                                          (unchecked-add (long (count (str (nth values vi)))) 1)
                                          1))
                            :pad-byte 1
                            :align-only 0
                            (:int :uint) size
                            (:float) 4
                            (:double) 8
                            16))
              _ (when (> added (unchecked-subtract Long/MAX_VALUE pos))
                  (pack-error "format result too long"))
              needed (unchecked-add pos added)
              out-buf (if (> needed (alength ^bytes out-buf))
                        (let [new-buf (byte-array (int (* 2 needed)))]
                          (System/arraycopy out-buf 0 new-buf 0 (int pos))
                          new-buf)
                        out-buf)]
          ;; Write padding zeros
          (dotimes [k pad]
            (aset ^bytes out-buf (int (unchecked-add (unchecked-subtract pos pad) k)) (byte 0)))
          (case op
            (:int :uint)
            (let [v (long (nth values vi))
                  _ (check-pack-range v size signed?)]
              (write-int-bytes out-buf pos v size endian signed?)
              (recur (unchecked-inc di) (unchecked-inc vi) (unchecked-add pos size) out-buf))

            :float
            (let [v (double (nth values vi))]
              (write-float-bytes out-buf pos v endian)
              (recur (unchecked-inc di) (unchecked-inc vi) (unchecked-add pos 4) out-buf))

            :double
            (let [v (double (nth values vi))]
              (write-double-bytes out-buf pos v endian)
              (recur (unchecked-inc di) (unchecked-inc vi) (unchecked-add pos 8) out-buf))

            :fixed-str
            (let [s (str (nth values vi))
                  sbytes (str->bytes s)
                  slen (long (alength sbytes))]
              (when (> slen size)
                (pack-error (str "string longer than given size")))
              (System/arraycopy sbytes 0 out-buf (int pos) (int slen))
              ;; pad with zeros
              (dotimes [k (unchecked-subtract size slen)]
                (aset ^bytes out-buf (int (unchecked-add pos (unchecked-add slen k))) (byte 0)))
              (recur (unchecked-inc di) (unchecked-inc vi) (unchecked-add pos size) out-buf))

            :len-str
            (let [s (str (nth values vi))
                  sbytes (str->bytes s)
                  slen (long (alength sbytes))
                  ;; Check string length fits in prefix
                  _ (when (and (< size 8)
                               (>= slen (bit-shift-left 1 (int (* size 8)))))
                      (pack-error (str "string length does not fit in given size")))
                  ;; Ensure buffer
                  total (unchecked-add pos (unchecked-add size slen))
                  out-buf (if (> total (alength ^bytes out-buf))
                            (let [new-buf (byte-array (int (* 2 total)))]
                              (System/arraycopy out-buf 0 new-buf 0 (int pos))
                              new-buf)
                            out-buf)]
              ;; Write length prefix
              (write-int-bytes out-buf pos slen size endian false)
              ;; Write string content
              (System/arraycopy sbytes 0 out-buf (int (unchecked-add pos size)) (int slen))
              (recur (unchecked-inc di) (unchecked-inc vi) (unchecked-add pos (unchecked-add size slen)) out-buf))

            :zstr
            (let [s (str (nth values vi))
                  sbytes (str->bytes s)
                  slen (long (alength sbytes))
                  ;; Check for embedded zeros
                  _ (loop [k (long 0)]
                      (when (< k slen)
                        (when (zero? (aget sbytes (int k)))
                          (pack-error "string contains zeros"))
                        (recur (unchecked-inc k))))
                  total (unchecked-add pos (unchecked-add slen 1))
                  out-buf (if (> total (alength ^bytes out-buf))
                            (let [new-buf (byte-array (int (* 2 total)))]
                              (System/arraycopy out-buf 0 new-buf 0 (int pos))
                              new-buf)
                            out-buf)]
              (System/arraycopy sbytes 0 out-buf (int pos) (int slen))
              (aset ^bytes out-buf (int (unchecked-add pos slen)) (byte 0))
              (recur (unchecked-inc di) (unchecked-inc vi) (unchecked-add pos (unchecked-add slen 1)) out-buf))

            :pad-byte
            (do
              (aset ^bytes out-buf (int pos) (byte 0))
              (recur (unchecked-inc di) vi (unchecked-inc pos) out-buf))

            :align-only
            (recur (unchecked-inc di) vi pos out-buf)))))))

;; --- unpack -----------------------------------------------------------------

(defn lua-unpack
  "string.unpack(fmt, s [, pos]) - Unpack values from binary string.
   Returns unpacked values followed by position after last read byte."
  [fmt s & [pos]]
  (let [fmt (str fmt)
        s (str s)
        buf (str->bytes s)
        buf-len (long (alength buf))
        directives (parse-format fmt)
        ;; Handle position: 1-indexed, negative counts from end
        raw-pos (long (or pos 1))
        offset (long (if (neg? raw-pos)
                       (unchecked-add buf-len raw-pos)      ;; negative: len + pos (pos is negative)
                       (unchecked-dec raw-pos)))            ;; positive: 0-indexed
        _ (when (or (< offset 0) (> offset buf-len))
            (pack-error "initial position out of string"))]
    (loop [di (long 0)
           pos offset
           results []]
      (if (>= di (count directives))
        (conj results (unchecked-inc pos))                  ;; return 1-indexed position after last byte
        (let [{:keys [op size endian actual-align signed?]} (nth directives di)
              size (long size)
              actual-align (long actual-align)
              ;; Apply alignment padding
              pad (long (align-padding pos (long (Math/max 1 actual-align))))
              pos (long (unchecked-add pos pad))]
          (case op
            (:int :uint)
            (do
              (when (> (unchecked-add pos size) buf-len)
                (pack-error "data string too short"))
              (let [v (read-int-bytes buf pos size endian signed?)]
                (recur (unchecked-inc di) (long (unchecked-add pos size)) (conj results v))))

            :float
            (do
              (when (> (unchecked-add pos 4) buf-len)
                (pack-error "data string too short"))
              (let [v (read-float-bytes buf pos endian)]
                (recur (unchecked-inc di) (long (unchecked-add pos 4)) (conj results v))))

            :double
            (do
              (when (> (unchecked-add pos 8) buf-len)
                (pack-error "data string too short"))
              (let [v (read-double-bytes buf pos endian)]
                (recur (unchecked-inc di) (long (unchecked-add pos 8)) (conj results v))))

            :fixed-str
            (do
              (when (> (unchecked-add pos size) buf-len)
                (pack-error "data string too short"))
              (let [v (bytes->str buf pos size)]
                (recur (unchecked-inc di) (long (unchecked-add pos size)) (conj results v))))

            :len-str
            (do
              (when (> (unchecked-add pos size) buf-len)
                (pack-error "data string too short"))
              (let [slen (long (read-int-bytes buf pos size endian false))
                    data-start (long (unchecked-add pos size))]
                (when (or (neg? slen) (> (unchecked-add data-start slen) buf-len))
                  (pack-error "data string too short"))
                (let [v (bytes->str buf data-start slen)]
                  (recur (unchecked-inc di) (long (unchecked-add data-start slen)) (conj results v)))))

            :zstr
            (let [null-pos (long (loop [k pos]
                                   (cond
                                     (>= k buf-len) (pack-error "unfinished string for format 'z'")
                                     (zero? (aget buf (int k))) k
                                     :else (recur (unchecked-inc k)))))
                  v (bytes->str buf pos (unchecked-subtract null-pos pos))]
              (recur (unchecked-inc di) (unchecked-inc null-pos) (conj results v)))

            :pad-byte
            (do
              (when (> (unchecked-inc pos) buf-len)
                (pack-error "data string too short"))
              (recur (unchecked-inc di) (unchecked-inc pos) results))

            :align-only
            (recur (unchecked-inc di) pos results)))))))

;; --- packsize ---------------------------------------------------------------

(defn lua-packsize
  "string.packsize(fmt) - Returns size of packed string for format.
   Rejects variable-length formats (s, z)."
  [fmt]
  (let [fmt (str fmt)
        directives (parse-format fmt :reject-variable true)]
    (loop [di (long 0)
           pos (long 0)]
      (if (>= di (count directives))
        pos
        (let [{:keys [op size actual-align]} (nth directives di)
              size (long size)
              actual-align (long actual-align)
              pad (long (align-padding pos (long (Math/max 1 actual-align))))
              _ (when (> pad (unchecked-subtract Long/MAX_VALUE pos))
                  (pack-error "format result too large"))
              pos (unchecked-add pos pad)
              added (long (case op
                            (:int :uint) size
                            :float 4
                            :double 8
                            :fixed-str size
                            :pad-byte 1
                            :align-only 0
                            0))
              _ (when (> added (unchecked-subtract Long/MAX_VALUE pos))
                  (pack-error "format result too large"))]
          (recur (unchecked-inc di) (unchecked-add pos added)))))))

;; =============================================================================
;; Export as Lua library table
;; =============================================================================

(defn lua-dump
  "string.dump(function) - not supported in CLua (would allow code serialization).
   Always throws an error, so pcall(string.dump, f) correctly returns false."
  [& _]
  (throw (ex-info "unable to dump given function" {:type :error})))

(def string-lib
  "The complete string library for Lua."
  {"len" lua-len
   "sub" lua-sub
   "upper" lua-upper
   "lower" lua-lower
   "rep" lua-rep
   "byte" lua-byte
   "char" lua-char
   "reverse" lua-reverse
   "format" lua-format
   "find" lua-find
   "match" lua-match
   "gmatch" lua-gmatch
   "gsub" lua-gsub
   "pack" lua-pack
   "unpack" lua-unpack
   "packsize" lua-packsize
   "dump" lua-dump})
