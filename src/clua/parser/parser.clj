(ns clua.parser.parser
  "Lua parser using ANTLR4.

   Parses Lua source code into an AST suitable for interpretation.

   Grammar source: Lua 5.3 Reference Manual via grammars-v4
   See resources/Lua.g4 for ANTLR grammar"
  (:require [clojure.string :as str]
            [clua.parser.antlr-transform :as antlr-transform]
            [clua.interpreter.const-check :as const-check]
            [clua.parser.parser-antlr :as antlr]))

(set! *warn-on-reflection* true)


;; ============================================================================
;; Lua literal parsing helpers
;; ============================================================================

(defn- encode-raw-chars
  "Re-encode non-ASCII chars as UTF-8 bytes (each byte stored as a Java char 0–255).
   Used for long string literals and the regular-char path in parse-escape-sequences.
   Handles ANTLR surrogate pairs for supplementary codepoints (U+10000–U+10FFFF)."
  [^String s]
  (let [len (.length s)
        sb (StringBuilder.)]
    (loop [i 0]
      (if (>= i len)
        (str sb)
        (let [ch (.charAt s i)
              code (int ch)]
          (if (and (>= code 0xD800) (<= code 0xDBFF) (< (inc i) len))
            ;; Surrogate pair: encode as UTF-8 bytes
            (let [low (.charAt s (inc i))
                  codepoint (Character/toCodePoint ch low)
                  utf8-bytes (.getBytes (String. (Character/toChars codepoint)) "UTF-8")]
              (doseq [b utf8-bytes]
                (.append sb (char (Byte/toUnsignedInt b))))
              (recur (+ i 2)))
            ;; Direct storage: char value IS the Lua byte value
            (do (.append sb ch) (recur (inc i)))))))))

(defn- encode-codepoint-utf8!
  "Append the UTF-8 byte encoding of codepoint cp (0–0x7FFFFFFF) to sb.
   Uses the original multi-byte UTF-8 extension for values > 0x10FFFF."
  [^StringBuilder sb ^long cp]
  (cond
    (<= cp 0x7F)
    (.append sb (char cp))
    (<= cp 0x7FF)
    (do (.append sb (char (bit-or 0xC0 (bit-shift-right cp 6))))
        (.append sb (char (bit-or 0x80 (bit-and cp 0x3F)))))
    (<= cp 0xFFFF)
    (do (.append sb (char (bit-or 0xE0 (bit-shift-right cp 12))))
        (.append sb (char (bit-or 0x80 (bit-and (bit-shift-right cp 6) 0x3F))))
        (.append sb (char (bit-or 0x80 (bit-and cp 0x3F)))))
    (<= cp 0x1FFFFF)
    (do (.append sb (char (bit-or 0xF0 (bit-shift-right cp 18))))
        (.append sb (char (bit-or 0x80 (bit-and (bit-shift-right cp 12) 0x3F))))
        (.append sb (char (bit-or 0x80 (bit-and (bit-shift-right cp 6) 0x3F))))
        (.append sb (char (bit-or 0x80 (bit-and cp 0x3F)))))
    (<= cp 0x3FFFFFF)
    (do (.append sb (char (bit-or 0xF8 (bit-shift-right cp 24))))
        (.append sb (char (bit-or 0x80 (bit-and (bit-shift-right cp 18) 0x3F))))
        (.append sb (char (bit-or 0x80 (bit-and (bit-shift-right cp 12) 0x3F))))
        (.append sb (char (bit-or 0x80 (bit-and (bit-shift-right cp 6) 0x3F))))
        (.append sb (char (bit-or 0x80 (bit-and cp 0x3F)))))
    :else                                                   ;; 0x4000000–0x7FFFFFFF: 6-byte
    (do (.append sb (char (bit-or 0xFC (bit-shift-right cp 30))))
        (.append sb (char (bit-or 0x80 (bit-and (bit-shift-right cp 24) 0x3F))))
        (.append sb (char (bit-or 0x80 (bit-and (bit-shift-right cp 18) 0x3F))))
        (.append sb (char (bit-or 0x80 (bit-and (bit-shift-right cp 12) 0x3F))))
        (.append sb (char (bit-or 0x80 (bit-and (bit-shift-right cp 6) 0x3F))))
        (.append sb (char (bit-or 0x80 (bit-and cp 0x3F)))))))

(defn- parse-escape-sequences
  "Process Lua escape sequences in a short string (without quotes).
   Lua 5.3/5.4 escape sequences:
   \\a (bell), \\b (backspace), \\f (form feed), \\n (newline),
   \\r (carriage return), \\t (tab), \\v (vertical tab),
   \\\\ (backslash), \\\" (quote), \\' (apostrophe),
   \\z (skip whitespace), \\xXX (hex byte), \\ddd (decimal byte),
   \\u{XXX} (UTF-8 codepoint, 0–0x7FFFFFFF)

   close-quote: the closing delimiter of the string (\\\" or \\'), used for error messages."
  [s close-quote]
  (let [len (count s)
        sb (StringBuilder.)]
    (loop [i 0]
      (if (>= i len)
        (str sb)
        (let [ch (nth s i)]
          (if (not= ch \\)
            ;; Regular character: store raw byte value directly
            (let [code (int ch)]
              (cond
                (and (>= code 0xD800) (<= code 0xDBFF) (< (inc i) len))
                ;; Surrogate pair: compute codepoint and encode as UTF-8 bytes
                (let [low (nth s (inc i))
                      codepoint (Character/toCodePoint ch low)]
                  (encode-codepoint-utf8! sb codepoint)
                  (recur (+ i 2)))

                (> code 255)
                ;; Non-ASCII, non-surrogate char (e.g. U+FFFD from invalid UTF-8 in source):
                ;; encode as UTF-8 bytes so the result is a valid Lua byte sequence
                (do (encode-codepoint-utf8! sb code) (recur (inc i)))

                :else
                ;; Direct storage: char value IS the Lua byte value (0-255)
                (do (.append sb ch) (recur (inc i)))))
            ;; Escape sequence
            (if (>= (inc i) len)
              ;; Trailing backslash - keep it
              (do (.append sb ch)
                  (recur (inc i)))
              (let [next-ch (nth s (inc i))]
                (cond
                  ;; Simple escapes - check for the LETTER, not the character it represents
                  (= next-ch (first "a")) (do (.append sb \u0007) (recur (+ i 2))) ; bell
                  (= next-ch (first "b")) (do (.append sb \u0008) (recur (+ i 2))) ; backspace
                  (= next-ch (first "f")) (do (.append sb \u000C) (recur (+ i 2))) ; form feed
                  (= next-ch (first "n")) (do (.append sb \newline) (recur (+ i 2))) ; newline
                  (= next-ch (first "r")) (do (.append sb \return) (recur (+ i 2))) ; return
                  (= next-ch (first "t")) (do (.append sb \tab) (recur (+ i 2))) ; tab
                  (= next-ch (first "v")) (do (.append sb \u000B) (recur (+ i 2))) ; vertical tab
                  (= next-ch \\) (do (.append sb \\) (recur (+ i 2)))
                  (= next-ch \") (do (.append sb \") (recur (+ i 2)))
                  (= next-ch \') (do (.append sb \') (recur (+ i 2)))

                  ;; Also handle backslash + actual newline/return/tab (for multiline strings)
                  (= next-ch \newline) (do (.append sb \newline) (recur (+ i 2)))
                  (= next-ch \return) (do (.append sb \return) (recur (+ i 2)))
                  (= next-ch \tab) (do (.append sb \tab) (recur (+ i 2)))

                  ;; \z - skip following whitespace
                  (= next-ch \z)
                  (let [skip-end (loop [j (+ i 2)]
                                   (if (and (< j len)
                                            (Character/isWhitespace (int (nth s j))))
                                     (recur (inc j))
                                     j))]
                    (recur (long skip-end)))

                  ;; \xXX - hex byte (exactly 2 hex digits)
                  (= next-ch \x)
                  (if (> (+ i 4) len)
                    ;; Not enough chars for \xXX
                    (do (.append sb ch)
                        (recur (inc i)))
                    (let [hex-str (subs s (+ i 2) (+ i 4))]
                      (if (re-matches #"[0-9a-fA-F]{2}" hex-str)
                        (do (.append sb (char (Integer/parseInt hex-str 16)))
                            (recur (+ i 4)))
                        ;; Invalid hex, keep backslash
                        (do (.append sb ch)
                            (recur (inc i))))))

                  ;; \u{XXX} - UTF-8 codepoint (0–0x7FFFFFFF per Lua 5.4)
                  (= next-ch \u)
                  (if (and (< (+ i 3) len)
                           (= \{ (nth s (+ i 2))))
                    ;; Find closing brace
                    (let [close-idx (str/index-of s "}" (+ i 3))]
                      (if close-idx
                        (let [hex-str (subs s (+ i 3) close-idx)]
                          (if (re-matches #"[0-9a-fA-F]+" hex-str)
                            (let [codepoint (try (Long/parseLong hex-str 16)
                                                 (catch NumberFormatException _ (inc (long 0x7FFFFFFF))))]
                              (if (<= (long codepoint) 0x7FFFFFFF)
                                (do (encode-codepoint-utf8! sb codepoint)
                                    (recur (inc (long close-idx))))
                                ;; Codepoint too large
                                (throw (ex-info (str "near '" (subs s 0 close-idx) "'")
                                                {:type :parse-error}))))
                            ;; Invalid hex
                            (do (.append sb ch)
                                (recur (inc i)))))
                        ;; No closing brace
                        (do (.append sb ch)
                            (recur (inc i)))))
                    ;; Not \u{
                    (do (.append sb ch)
                        (recur (inc i))))

                  ;; Check for decimal escape \ddd (1-3 digits)
                  (Character/isDigit (int next-ch))
                  (let [digits (loop [j (inc i) acc []]
                                 (if (and (< j len)
                                          (< (count acc) 3)
                                          (Character/isDigit (int (nth s j))))
                                   (recur (inc j) (conj acc (nth s j)))
                                   acc))
                        num-str (apply str digits)
                        value (Integer/parseInt num-str)]
                    (if (<= value 255)
                      (do (.append sb (char value))
                          (recur (+ i 1 (count digits))))
                      (throw (ex-info (str "near '" (subs s 0 (+ i 1 (count digits))) close-quote "'")
                                      {:type :parse-error}))))

                  ;; Unknown escape - keep the backslash and character
                  :else
                  (do (.append sb ch)
                      (.append sb next-ch)
                      (recur (+ i 2))))))))))))
;; ============================================================================
;; Malformed-number pre-scan
;; ============================================================================

(defn- hex-digit? [c]
  (let [i (int (char c))]
    (or (and (>= i 48) (<= i 57))                           ; 0-9
        (and (>= i 97) (<= i 102))                          ; a-f
        (and (>= i 65) (<= i 70)))))                        ; A-F

(defn- decimal-digit? [c]
  (let [i (int (char c))]
    (and (>= i 48) (<= i 57))))                             ; 0-9

(defn- alpha-underscore? [c]
  (let [c (char c)]
    (or (Character/isLetter c) (= c \_))))

(defn- scan-hex-digits [^String s ^long p ^long len]
  (loop [i p] (if (and (< i len) (hex-digit? (.charAt s i))) (recur (unchecked-inc i)) i)))

(defn- scan-decimal-digits [^String s ^long p ^long len]
  (loop [i p] (if (and (< i len) (decimal-digit? (.charAt s i))) (recur (unchecked-inc i)) i)))

(defn- scan-number-token
  "Scan a number literal starting at pos. Returns [end-pos malformed?].
   malformed? is true when the exponent part is incomplete (digits missing after sign)."
  [^String s ^long pos ^long len]
  (let [hex? (and (> (- len pos) 1)
                  (= \0 (.charAt s pos))
                  (let [c (.charAt s (inc pos))] (or (= c \x) (= c \X))))]
    (if hex?
      (let [p3 (long (scan-hex-digits s (+ pos 2) len))
            p4 (long (if (and (< p3 len) (= \. (.charAt s p3)))
                       (scan-hex-digits s (unchecked-inc p3) len)
                       p3))]
        (if (and (< p4 len) (let [c (.charAt s p4)] (or (= c \p) (= c \P))))
          (let [pp (unchecked-inc p4)
                pp2 (long (if (and (< pp len) (let [c (.charAt s pp)] (or (= c \+) (= c \-)))) (unchecked-inc pp) pp))
                pp3 (long (scan-decimal-digits s pp2 len))]
            (if (= pp3 pp2) [pp2 true] [pp3 false]))
          [p4 false]))
      ;; decimal
      (let [p2 (long (if (and (< pos len) (= \. (.charAt s pos)))
                       (scan-decimal-digits s (unchecked-inc pos) len)
                       (let [pi (long (scan-decimal-digits s pos len))]
                         (if (and (< pi len) (= \. (.charAt s pi)))
                           (scan-decimal-digits s (unchecked-inc pi) len)
                           pi))))]
        (if (and (< p2 len) (let [c (.charAt s p2)] (or (= c \e) (= c \E))))
          (let [pp (unchecked-inc p2)
                pp2 (long (if (and (< pp len) (let [c (.charAt s pp)] (or (= c \+) (= c \-)))) (unchecked-inc pp) pp))
                pp3 (long (scan-decimal-digits s pp2 len))]
            (if (= pp3 pp2) [pp2 true] [pp3 false]))
          [p2 false])))))

(defn- skip-short-str [^String s ^long pos ^long len]
  (let [q (.charAt s pos)]
    (loop [p (inc pos)]
      (cond (>= p len) p
            (= \\ (.charAt s p)) (recur (min len (+ p 2)))
            (= q (.charAt s p)) (inc p)
            :else (recur (inc p))))))

(defn- skip-long-bracket-content [^String s ^long pos ^long len]
  ;; pos is the '[' that starts the bracket
  (loop [p (inc pos) n 0]
    (cond
      (>= p len) -1
      (= \= (.charAt s p)) (recur (inc p) (inc n))
      (= \[ (.charAt s p)) (let [close (str "]" (str/join (repeat n "=")) "]")
                                 ci (.indexOf s ^String close (int (inc p)))]
                             (if (neg? ci) len (+ ci (count close))))
      :else -1)))

(defn- check-malformed-numbers
  "Pre-scan source for number literals immediately followed by a letter or
   underscore, or with an incomplete exponent. Throws ex-info with a
   'malformed number near X' message if found."
  [^String source]
  (let [len (long (count source))]
    (loop [pos (long 0)]
      (when (< pos len)
        (let [ch (.charAt source pos)]
          (cond
            (or (= ch \") (= ch \'))
            (recur (long (skip-short-str source pos len)))

            (= ch \[)
            (let [end (long (skip-long-bracket-content source pos len))]
              (recur (if (neg? end) (inc pos) end)))

            (and (= ch \-) (< (inc pos) len) (= \- (.charAt source (inc pos))))
            ;; comment
            (let [p (+ pos 2)]
              (if (and (< p len) (= \[ (.charAt source p)))
                (let [end (long (skip-long-bracket-content source p len))]
                  (recur (if (neg? end)
                           (let [nl (.indexOf source (int \newline) (int pos))]
                             (if (neg? nl) len (inc (long nl))))
                           end)))
                (let [nl (.indexOf source (int \newline) (int pos))]
                  (recur (if (neg? nl) len (inc (long nl)))))))

            ;; Skip identifiers/keywords: letter or underscore starts an ident;
            ;; skip the whole ident so we don't match digits inside it (e.g. l3_1).
            (alpha-underscore? ch)
            (let [end (loop [p (inc pos)]
                        (if (and (< p len)
                                 (let [c (.charAt source p)]
                                   (or (alpha-underscore? c) (decimal-digit? c))))
                          (recur (inc p))
                          p))]
              (recur (long end)))

            (decimal-digit? ch)
            (let [[end-pos mal?] (scan-number-token source pos len)
                  end-pos (long end-pos)
                  next-is-alpha (and (< end-pos len) (alpha-underscore? (.charAt source end-pos)))]
              (when (or mal? next-is-alpha)
                (let [nc (if (< end-pos len) (.charAt source end-pos) \space)
                      sb (StringBuilder.)]
                  (when (or (alpha-underscore? nc) (decimal-digit? nc))
                    (.append sb nc)
                    (loop [p (inc end-pos)]
                      (when (and (< p len)
                                 (let [c (.charAt source p)]
                                   (or (alpha-underscore? c) (decimal-digit? c))))
                        (.append sb (.charAt source p))
                        (recur (inc p)))))
                  (throw (ex-info (str "malformed number near '" (if (pos? (.length sb)) (str sb) (str nc)) "'")
                                  {:type :parse-error :line 1}))))
              (recur end-pos))

            :else (recur (inc pos))))))))

;; Per-compilation string deduplication table.
;; Bound to a fresh atom for each parse-and-transform call so that identical
;; string literals within the same source chunk share the same Java String object
;; (same System/identityHashCode → same %p address).  Runtime-computed strings
;; (concatenation, string.rep, etc.) are created after parse time, so they are
;; NOT deduplicated and have distinct identity → different %p addresses.
(def ^:dynamic *literal-string-table* nil)

(defn- intern-literal
  "Return a canonical String object for s within the current compilation unit.
   If *literal-string-table* is bound (during parse-and-transform), reuses the
   same object for equal content.  Otherwise returns s unchanged."
  [s]
  (if-let [t *literal-string-table*]
    (or (get @t s)
        (do (swap! t assoc s s) s))
    s))

(defn- parse-lua-string
  "Parse a Lua string literal, handling quotes and escape sequences."
  [s]
  (cond
    ;; Long string [[...]] or [=[...]=] - no escape processing
    (re-matches #"\[=*\[[\s\S]*\]=*\]" s)
    (let [eq-count (count (re-find #"^\[=*" s))
          start (inc eq-count)
          end (- (count s) (inc eq-count))
          content (subs s start end)
          ;; Lua specification: "A line break immediately following the opening bracket is discarded"
          stripped (if (and (pos? (count content))
                            (or (= (first content) \newline)
                                (and (= (first content) \return)
                                     (or (= (count content) 1)
                                         (not= (second content) \newline)))))
                     (subs content 1)
                     content)]
      (intern-literal (encode-raw-chars stripped)))

    ;; Short string 'x' or "x" - both support all escape sequences
    :else
    (intern-literal (parse-escape-sequences (subs s 1 (dec (count s))) (last s)))))

(defn- parse-lua-number
  "Parse a Lua numeric literal (decimal, hex, float, hex float)."
  [s]
  (cond
    ;; Hex float with p exponent
    (re-matches #"(?i)0x[0-9a-f]*\.?[0-9a-f]*p[+-]?[0-9]+" s)
    (let [[_ mantissa exp] (re-matches #"(?i)0x([0-9a-f]*\.?[0-9a-f]*)p([+-]?[0-9]+)" s)
          base (double (if (str/includes? mantissa ".")
                         (let [[int-part frac-part] (str/split mantissa #"\.")]
                           (+ (double (if (seq int-part) (Integer/parseInt int-part 16) 0))
                              (/ (Integer/parseInt (or frac-part "0") 16)
                                 (Math/pow 16 (count (or frac-part ""))))))
                         (Integer/parseInt mantissa 16)))]
      (* base (Math/pow 2 (Integer/parseInt exp))))

    ;; Hex float with dot but no p exponent (e.g., 0x.41, 0x1.2)
    (re-matches #"(?i)0x[0-9a-f]*\.[0-9a-f]*" s)
    (let [[_ int-part frac-part] (re-matches #"(?i)0x([0-9a-f]*)\.([0-9a-f]*)" s)
          int-val (if (seq int-part) (Long/parseLong int-part 16) 0)
          frac-val (if (seq frac-part)
                     (/ (double (Long/parseLong frac-part 16))
                        (Math/pow 16 (count frac-part)))
                     0.0)]
      (double (+ int-val frac-val)))

    ;; Hex integer - wraps modulo 2^64 like Lua 5.3's C implementation
    (re-matches #"(?i)0x[0-9a-f]+" s)
    (.longValue (BigInteger. (subs s 2) 16))

    ;; Decimal float or integer
    :else
    (if (or (str/includes? s ".")
            (str/includes? s "e")
            (str/includes? s "E"))
      (Double/parseDouble s)
      (try
        (Long/parseLong s)
        (catch NumberFormatException _
          ;; Try as unsigned 64-bit (handles overflow like 9223372036854775808 → Long.MIN_VALUE)
          ;; This matches Lua 5.3 integer literal wrapping semantics
          (try
            (Long/parseUnsignedLong s)
            (catch NumberFormatException _
              (Double/parseDouble s))))))))

;; ============================================================================
;; AST Transformation
;; ============================================================================

(defn- apply-suffix
  "Apply a single suffix to an expression."
  [expr suffix]
  (cond
    (= :index (:suffix-type suffix))
    {:type :index-access :object expr :index (:index suffix)}

    (= :field (:suffix-type suffix))
    {:type :field-access :object expr :field (:field suffix)}

    (= :call (:suffix-type suffix))
    {:type :function-call :target expr :args (:args suffix)}

    (= :method (:suffix-type suffix))
    {:type :method-call :object expr :method (:method suffix) :args (:args suffix)}

    :else expr))

(defn- apply-suffixes
  "Apply a sequence of suffixes to a base expression."
  [base suffixes]
  (reduce apply-suffix base suffixes))

(def ^:private ast-transformers
  "Map of parse tree node types to their transformation functions."
  {;; Top-level
   :chunk (fn [& body] {:type :chunk :body (vec body)})
   :block (fn [& stmts]
            ;; Add statement indices for position tracking
            {:type :block
             :statements (vec (map-indexed
                                (fn [idx stmt]
                                  (if (map? stmt)
                                    (assoc stmt :stmt-index idx)
                                    stmt))
                                stmts))})
   :stat (fn ([] {:type :nop}) ([x] x))                     ; empty for ';' only

   ;; Control flow statements
   :break-stat (fn [] {:type :break})
   :goto-stat (fn [name] {:type :goto :label name})
   :do-stat (fn [body] {:type :do :body body})
   :while-stat (fn [cond body] {:type :while :condition cond :body body})
   :repeat-stat (fn [body cond] {:type :repeat :body body :condition cond})
   :if-stat (fn [cond then-block & rest]
              {:type :if
               :condition cond
               :then then-block
               :elseifs (vec (filter #(= :elseif (:type %)) rest))
               :else (first (filter #(= :else (:type %)) rest))})
   :elseif-clause (fn [cond body] {:type :elseif :condition cond :body body})
   :else-clause (fn [body] {:type :else :body body})
   :for-numeric (fn [var start end & rest]
                  (let [has-step (> (count rest) 1)
                        step (if has-step (first rest) {:type :number :value 1})
                        body (last rest)]
                    {:type :for-numeric :var var :start start :end end :step step :body body}))
   :for-generic (fn [names exps body]
                  {:type :for-generic :names names :expressions exps :body body})
   :func-stat (fn [fname fbody]
                {:type :func-def-stat :name fname :body fbody})
   :local-func-stat (fn [name fbody]
                      {:type :local-func-def :name name :body fbody})
   :local-stat (fn [names & values]
                 {:type :local :names names :values (first values)})
   :global-func-stat (fn [fname fbody] {:type :global-func-def :name fname :body fbody})
   :global-none (fn [] {:type :global-none})
   :global-wildcard (fn [& [attrib]] (if attrib {:type :global-wildcard :attrib (keyword attrib)} {:type :global-wildcard}))
   :global-decl (fn [names & values]
                  {:type :global-decl :names names :values (first values)})

   ;; Terminals
   :Name (fn [n] {:type :name :value n})
   :NameAttr (fn [n attrib] {:type :name :value n :attrib (keyword attrib)})
   :Numeral (fn [& parts] {:type :number :value (parse-lua-number (apply str parts))})
   :Integer identity
   :Float identity
   :HexInteger identity
   :HexFloat identity
   :LiteralString (fn [s] {:type :string :value (parse-lua-string s)})
   :ShortString identity
   :LongString identity

   ;; Literals
   :nil-lit (fn [] {:type :nil})
   :false-lit (fn [] {:type :boolean :value false})
   :true-lit (fn [] {:type :boolean :value true})
   :vararg-lit (fn [] {:type :vararg})

   ;; Lists
   :explist (fn [& exps] {:type :exp-list :values (vec exps)})
   :namelist (fn [& names] {:type :name-list :names (vec names)})

   ;; Operators (legacy)
   :binop (fn [op] {:type :binop :op (str op)})
   :unop (fn [op] {:type :unop :op (str op)})

   ;; Operator tokens for precedence levels
   :or-op (fn [_] "or")
   :and-op (fn [_] "and")
   :cmp-op (fn [op] (str op))
   :bitor-op (fn [op] (str op))
   :bitxor-op (fn [op] (str op))
   :bitand-op (fn [op] (str op))
   :shift-op (fn [op] (str op))
   :concat-op (fn [op] (str op))
   :add-op (fn [op] (str op))
   :mul-op (fn [op] (str op))
   :power-op (fn [op] (str op))

   ;; Suffixes
   :indexsuffix (fn [idx] {:suffix-type :index :index idx})
   :fieldsuffix (fn [name] {:suffix-type :field :field name})
   :suffix (fn [& parts]
             ;; suffix can be: indexsuffix, fieldsuffix, args, or ':' Name args
             (let [first-part (first parts)]
               (cond
                 ;; Already transformed suffix (indexsuffix or fieldsuffix)
                 (:suffix-type first-part)
                 first-part

                 ;; args - mark as call suffix
                 (= :args (:type first-part))
                 {:suffix-type :call :args first-part}

                 ;; Method call: Name args
                 (and (= :name (:type first-part))
                      (= 2 (count parts)))
                 {:suffix-type :method :method first-part :args (second parts)}

                 :else first-part)))

   ;; Arguments
   :args (fn [& args]
           {:type :args :values (vec args)})

   ;; Call args (regular or method call)
   :callargs (fn [& parts]
               (if (= 2 (count parts))
                 ;; Method call: Name args
                 {:type :method-call :method (first parts) :args (second parts)}
                 ;; Regular call
                 {:type :call :args (first parts)}))

   ;; Call chain: suffixes leading to a call
   :callchain (fn [& parts]
                (if (= 1 (count parts))
                  ;; Just callargs
                  (first parts)
                  ;; suffix+ callargs
                  (let [suffixes (butlast parts)
                        callargs (last parts)]
                    {:type :chain :suffixes (vec suffixes) :final callargs})))

   ;; Function call statement
   :functioncall (fn [base chain]
                   (cond
                     ;; Simple call: name + callargs
                     (= :call (:type chain))
                     {:type :function-call :target base :args (:args chain)}

                     ;; Method call: name + method-call
                     (= :method-call (:type chain))
                     {:type :method-call :object base :method (:method chain) :args (:args chain)}

                     ;; Chain with suffixes
                     (= :chain (:type chain))
                     (let [with-suffixes (apply-suffixes base (:suffixes chain))
                           final (:final chain)]
                       (if (= :method-call (:type final))
                         {:type :method-call
                          :object with-suffixes
                          :method (:method final)
                          :args (:args final)}
                         {:type :function-call
                          :target with-suffixes
                          :args (:args final)}))

                     :else
                     {:type :function-call :target base :args chain}))

   ;; Method call from ANTLR format: [:methodcall object method args]
   :methodcall (fn [object method args]
                 {:type :method-call
                  :object object
                  :method method
                  :args args})

   ;; Variable reference (for assignment)
   :varref (fn [& parts]
             (let [base (first parts)
                   suffixes (rest parts)]
               (if (seq suffixes)
                 ;; Check if first suffix is a callchain (needs special handling)
                 (let [first-suffix (first suffixes)]
                   (if (or (= :call (:type first-suffix))
                           (= :method-call (:type first-suffix)))
                     ;; Have a call - create function/method call and apply remaining suffixes
                     (let [call-node (if (= :call (:type first-suffix))
                                       {:type :function-call
                                        :target base
                                        :args (:args first-suffix)}
                                       {:type :method-call
                                        :object base
                                        :method (:method first-suffix)
                                        :args (:args first-suffix)})
                           remaining (rest suffixes)]
                       (if (seq remaining)
                         (apply-suffixes call-node remaining)
                         call-node))
                     ;; Normal suffixes
                     (apply-suffixes base suffixes)))
                 base)))

   ;; Assignment
   :assignment (fn [& parts]
                 (let [vars (butlast parts)
                       values (last parts)]
                   {:type :assignment
                    :vars {:type :var-list :vars (vec vars)}
                    :values values}))

   ;; Prefix expression (in expression context)
   :prefixexp (fn [& parts]
                (let [base (first parts)
                      suffixes (rest parts)]
                  (if (seq suffixes)
                    (apply-suffixes base suffixes)
                    base)))

   ;; Parenthesized expression: (expr)
   ;; In Lua, (expr) truncates multiple return values to exactly one.
   :paren-exp (fn [inner] {:type :paren-exp :expr inner})

   ;; Helper to build left-associative binary expression chain
   ;; Input: [expr1 op1 expr2 op2 expr3 ...]
   ;; Output: nested {:type :binary-exp} left-to-right

   ;; Expression precedence levels (left-associative)
   :or-exp (fn [& parts]
             (if (= 1 (count parts))
               (first parts)
               (reduce (fn [left [op right]]
                         {:type :binary-exp :left left :op op :right right})
                       (first parts)
                       (partition 2 (rest parts)))))

   :and-exp (fn [& parts]
              (if (= 1 (count parts))
                (first parts)
                (reduce (fn [left [op right]]
                          {:type :binary-exp :left left :op op :right right})
                        (first parts)
                        (partition 2 (rest parts)))))

   :cmp-exp (fn [& parts]
              (if (= 1 (count parts))
                (first parts)
                (reduce (fn [left [op right]]
                          {:type :binary-exp :left left :op op :right right})
                        (first parts)
                        (partition 2 (rest parts)))))

   :bitor-exp (fn [& parts]
                (if (= 1 (count parts))
                  (first parts)
                  (reduce (fn [left [op right]]
                            {:type :binary-exp :left left :op op :right right})
                          (first parts)
                          (partition 2 (rest parts)))))

   :bitxor-exp (fn [& parts]
                 (if (= 1 (count parts))
                   (first parts)
                   (reduce (fn [left [op right]]
                             {:type :binary-exp :left left :op op :right right})
                           (first parts)
                           (partition 2 (rest parts)))))

   :bitand-exp (fn [& parts]
                 (if (= 1 (count parts))
                   (first parts)
                   (reduce (fn [left [op right]]
                             {:type :binary-exp :left left :op op :right right})
                           (first parts)
                           (partition 2 (rest parts)))))

   :shift-exp (fn [& parts]
                (if (= 1 (count parts))
                  (first parts)
                  (reduce (fn [left [op right]]
                            {:type :binary-exp :left left :op op :right right})
                          (first parts)
                          (partition 2 (rest parts)))))

   ;; Concatenation (right-associative) - grammar handles via recursion
   :concat-exp (fn [& parts]
                 (if (= 1 (count parts))
                   (first parts)
                   ;; parts: [left op right] where right is already a concat-exp
                   {:type :binary-exp
                    :left (first parts)
                    :op (second parts)
                    :right (nth parts 2)}))

   :add-exp (fn [& parts]
              (if (= 1 (count parts))
                (first parts)
                (reduce (fn [left [op right]]
                          {:type :binary-exp :left left :op op :right right})
                        (first parts)
                        (partition 2 (rest parts)))))

   :mul-exp (fn [& parts]
              (if (= 1 (count parts))
                (first parts)
                (reduce (fn [left [op right]]
                          {:type :binary-exp :left left :op op :right right})
                        (first parts)
                        (partition 2 (rest parts)))))

   ;; Unary expressions
   :unary-exp (fn [& parts]
                (if (= 1 (count parts))
                  (first parts)
                  ;; parts: [{:type :unop :op "-"} operand] or [op-string operand]
                  (let [op-part (first parts)
                        op (if (map? op-part)
                             (:op op-part)
                             (str op-part))]
                    {:type :unary-exp
                     :op op
                     :operand (second parts)})))

   ;; Power (right-associative) - grammar handles via recursion
   :power-exp (fn [& parts]
                (if (= 1 (count parts))
                  (first parts)
                  ;; parts: [base op exponent] where exponent is already a power-exp
                  {:type :binary-exp
                   :left (first parts)
                   :op (second parts)
                   :right (nth parts 2)}))

   ;; Primary expression - just pass through
   :primary-exp identity

   ;; Simple expressions (legacy fallback)
   :exp (fn [& parts]
          (cond
            (= 1 (count parts))
            (first parts)

            ;; Unary: unop exp
            (and (= 2 (count parts))
                 (= :unop (:type (first parts))))
            {:type :unary-exp
             :op (:op (first parts))
             :operand (second parts)}

            ;; Binary: exp binop exp
            (= 3 (count parts))
            {:type :binary-exp
             :left (first parts)
             :op (:op (second parts))
             :right (nth parts 2)}

            :else
            {:type :exp :parts (vec parts)}))

   ;; Control flow - inline patterns from stat
   ;; while
   ;; The stat rule captures these directly

   ;; Functions
   :functiondef (fn [body] {:type :function-def :body body})
   :funcbody (fn [& parts]
               (let [params (if (> (count parts) 1) (first parts) nil)
                     body (last parts)]
                 {:type :func-body :params params :body body}))
   :parlist (fn [& params] {:type :param-list :params (vec params)})
   :funcname (fn [first-name & parts]
               (let [names (vec (cons first-name (map second parts)))
                     method? (some #(= :colonname (first %)) parts)]
                 {:type :func-name :names names :method? method?}))
   :dotname (fn [name] [:dotname name])
   :colonname (fn [name] [:colonname name])

   ;; Tables
   :tableconstructor (fn [& fields] {:type :table :fields (vec fields)})
   :fieldlist (fn [& fields] (vec fields))
   :field (fn [& parts]
            (cond
              ;; [exp] = value - first part is "[", so 4 parts total
              (and (= 4 (count parts)) (= "[" (first parts)))
              {:type :bracket-field :key (second parts) :value (nth parts 3)}

              ;; name = value or exp
              (= 1 (count parts))
              {:type :array-field :value (first parts)}

              ;; Name = value - 2 parts
              (= 2 (count parts))
              {:type :name-field :name (first parts) :value (second parts)}))

   :label (fn [name] {:type :label :name name})
   :retstat (fn [& exps] {:type :return :values (first exps)})})

;; ============================================================================
;; ANTLR Parser Integration
;; ============================================================================

(defn- apply-ast-transformers
  "Apply AST transformers to an Instaparse-format tree.
   This is a simplified version that doesn't depend on instaparse.core/transform.
   Preserves metadata from the source tree and merges it into result maps."
  [tree]
  (if (vector? tree)
    (let [[tag & children] tree
          transformer (get ast-transformers tag)
          tree-meta (meta tree)
          result (if transformer
                   (apply transformer (map apply-ast-transformers children))
                   (into [tag] (map apply-ast-transformers children)))]
      ;; Preserve metadata if present
      (if tree-meta
        (if (map? result)
          ;; For maps, merge metadata as direct keys (for interpreter compatibility)
          (merge result tree-meta)
          ;; For vectors, attach as metadata
          (with-meta result tree-meta))
        result))
    tree))

(defn normalize-line-endings
  "Normalize all line endings in Lua source to Unix LF (\\n).

   Per Lua 5.3 spec, all of these are a single line break:
   - \\r\\n (CRLF), \\n\\r (LFCR), \\r alone, \\n alone.

   Normalizing before ANTLR parsing ensures:
   1. ANTLR counts line numbers correctly (it only increments for \\n).
   2. Long string content has consistent \\n line endings."
  [^String s]
  (let [chars (.toCharArray s)
        n (count chars)
        sb (StringBuilder. n)]
    (loop [i 0]
      (if (>= i n)
        (.toString sb)
        (let [c (aget chars i)]
          (cond
            (= c \return)
            (do (.append sb \newline)
                (if (and (< (inc i) n) (= (aget chars (inc i)) \newline))
                  (recur (+ i 2))
                  (recur (inc i))))
            (= c \newline)
            (do (.append sb \newline)
                (if (and (< (inc i) n) (= (aget chars (inc i)) \return))
                  (recur (+ i 2))
                  (recur (inc i))))
            :else
            (do (.append sb c)
                (recur (inc i)))))))))

(defn parse
  "Parse Lua source code using ANTLR4.
   Returns parse tree structure or error map."
  [source]
  (try
    (antlr/parse (normalize-line-endings source))
    (catch Exception e
      {:error true
       :message (.getMessage e)})))

;; ============================================================================
;; Goto Scope Validation (Lua 5.3 compile-time rules)
;; ============================================================================

(defn- get-sub-blocks-with-context
  "Returns a list of [stmts in-repeat?] pairs for nested blocks within stmt.
   Does NOT recurse into function bodies (they have separate label scopes).
   in-repeat? marks repeat bodies for stricter local-crossing checks."
  [stmt]
  (case (:type stmt)
    :repeat
    [[(get-in stmt [:body :statements]) true]]
    (:do :while :for-numeric :for-generic)
    [[(get-in stmt [:body :statements]) false]]
    :if
    (concat [[(get-in stmt [:then :statements]) false]]
            (map #(vector (get-in % [:body :statements]) false) (:elseifs stmt))
            (when-let [e (:else stmt)] [[(get-in e [:body :statements]) false]]))
    []))

(defn- first-local-name
  "Returns the first variable name introduced by a local or global-scope declaration, or nil."
  [stmt]
  (case (:type stmt)
    :local (-> stmt :names :names first :value)
    :local-func-def (:value (:name stmt))
    :global-wildcard "*"
    nil))

(defn- locals-between
  "Returns the first local variable name declared at positions strictly between
   from-pos and label-pos (exclusive). Returns nil for backward/same-position jumps."
  [stmts from-pos label-pos]
  (let [fp (long from-pos) lp (long label-pos)]
    (when (< fp lp)
      (first (keep (fn [[i stmt]]
                     (let [li (long i)]
                       (when (and (> li fp) (< li lp))
                         (first-local-name stmt))))
                   (map-indexed vector stmts))))))

(defn- label-at-end?
  "Returns true if no substantial statements (non-label, non-nop) exist after label-pos.
   Lua 5.3 allows forward jumps over locals when the label ends the block.
   Non-map entries (e.g. [nil] from ';') are treated as empty/non-substantial."
  [stmts label-pos]
  (let [lp (long label-pos)]
    (not (some (fn [[i stmt]]
                 (and (> (long i) lp)
                      (map? stmt)
                      (not (#{:label :nop} (:type stmt)))))
               (map-indexed vector stmts)))))

(defn- check-local-crossing
  "Throws ex-info if a forward jump from from-pos to label-pos crosses a local.
   In repeat bodies (in-repeat? = true), always errors.
   In other blocks, allows the jump when the label is at the end of the block."
  [stmts from-pos label-pos in-repeat?]
  (when-let [local-name (locals-between stmts from-pos label-pos)]
    (when (or in-repeat? (not (label-at-end? stmts label-pos)))
      (throw (ex-info (str "<goto> jumps into the scope of '" local-name "'")
                      {:type :goto-scope-error :local local-name})))))

(declare validate-function-labels)

(defn- validate-block-labels
  "Validates goto scopes within a block.
   visible: map of label-name → true for labels visible from parent blocks.
   in-repeat?: true when this is a repeat body (no 'label at end' exception).
   Returns seq of {:name label-name :from-pos i} for gotos unresolved at this level."
  [stmts visible in-repeat?]
  (let [indexed-stmts (map-indexed vector stmts)
        ;; Pass 1: collect direct labels and their positions, check for duplicates
        [my-labels label-positions]
        (reduce (fn [[labels positions] [i stmt]]
                  (if (= :label (:type stmt))
                    (let [lname (:value (:name stmt))]
                      (when (or (contains? labels lname) (contains? visible lname))
                        (let [first-line (or (get labels lname) (get visible lname))]
                          (throw (ex-info (str "label '" lname "' already defined on line " first-line)
                                          {:type :goto-scope-error :label lname :line (:line stmt)}))))
                      [(assoc labels lname (:line stmt)) (assoc positions lname i)])
                    [labels positions]))
                [{} {}]
                indexed-stmts)
        _all-visible (merge visible my-labels)]
    ;; Pass 2: walk statements resolving gotos
    (reduce (fn [pending [i stmt]]
              (cond
                (= :goto (:type stmt))
                (let [lname (:value (:label stmt))]
                  (if (contains? my-labels lname)
                    ;; Label owned by this block: check for local crossing
                    (do (check-local-crossing stmts i (label-positions lname) in-repeat?)
                        pending)
                    ;; Not owned here: propagate for parent to resolve
                    (conj pending {:name lname :from-pos i :goto-line (:line stmt)})))

                (#{:do :while :repeat :for-numeric :for-generic :if} (:type stmt))
                (let [;; Only include labels defined BEFORE this sub-block's position in visible.
                      ;; Labels after position i in the same block are not yet alive at this point.
                      visible-for-sub (reduce-kv (fn [acc nm pos]
                                                   (if (< (long pos) (long i)) (assoc acc nm (get my-labels nm)) acc))
                                                 visible label-positions)
                      sub-pending (mapcat (fn [[sub-stmts sub-in-repeat?]]
                                            (validate-block-labels sub-stmts visible-for-sub sub-in-repeat?))
                                          (get-sub-blocks-with-context stmt))]
                  (reduce (fn [p {:keys [name goto-line]}]
                            (if (contains? my-labels name)
                              ;; Label owned here: check local crossing using sub-block position i
                              (do (check-local-crossing stmts i (label-positions name) in-repeat?)
                                  p)
                              ;; Not owned here: propagate with from-pos = i (sub-block position)
                              (conj p {:name name :from-pos i :goto-line goto-line})))
                          pending sub-pending))

                (#{:func-def-stat :local-func-def} (:type stmt))
                (do (when-let [func-stmts (get-in stmt [:body :body :statements])]
                      (validate-function-labels func-stmts))
                    pending)

                :else pending))
            []
            indexed-stmts)))

(defn- validate-function-labels
  "Validates goto scopes for one function scope.
   Throws if any gotos remain unresolved after scanning the whole block."
  [stmts]
  (let [pending (validate-block-labels stmts {} false)]
    (when (seq pending)
      (let [{:keys [name goto-line]} (first pending)]
        (throw (ex-info (str "no visible label '" name "' for goto at line " goto-line)
                        {:type :goto-scope-error :label name}))))))

(defn- validate-goto-scopes
  "Entry point: validates compile-time goto/label scoping rules for a parsed AST.
   Throws ex-info on violation."
  [ast]
  (when-let [body (first (:body ast))]
    (validate-function-labels (:statements body))))

(defn- check-ast-limits
  "Enforce Lua 5.5 compile-time limits (matching LUAI_MAXCCALLS = 200):
   - Nesting depth of blocks, calls, constructors, parens, .. and ^ chains > 200
     → 'too many C levels'
   - Assignment target count > 200 → 'too many registers'
   gencode(100) must pass; gencode(500) must fail with 'too many' or 'overflow'."
  [ast]
  (let [limit (long 200)
        depth-nodes #{:do :while :for-numeric :for-generic :if :repeat
                      :func-def-stat :local-func-def :global-func-def :function-def}]
    (letfn [(walk-val [v ^long depth]
              (cond
                (map? v) (walk v depth)
                (vector? v) (doseq [item v] (walk-val item depth))
                :else nil))
            (walk [node ^long depth]
              (when (> depth limit)
                (throw (ex-info "too many C levels" {:type :parse-error})))
              (case (:type node)
                :assignment
                (do
                  (when (> (count (get-in node [:vars :vars])) limit)
                    (throw (ex-info "too many registers" {:type :parse-error})))
                  (walk-val (:values node) depth))

                :binary-exp
                (let [right-depth (if (#{".." "^"} (:op node)) (inc depth) depth)]
                  (walk (:left node) depth)
                  (walk (:right node) right-depth))

                :paren-exp
                (walk (:expr node) (inc depth))

                :table
                (walk-val (:fields node) (inc depth))

                (:function-call :method-call)
                (do
                  (walk-val (:target node) depth)
                  (walk-val (:object node) depth)
                  (walk-val (get-in node [:args :args]) (inc depth)))

                ;; Blocks and function defs increment depth for their body
                (if (depth-nodes (:type node))
                  (doseq [[k v] node]
                    (when (not= k :type)
                      (walk-val v (inc depth))))
                  (doseq [[k v] node]
                    (when (not= k :type)
                      (walk-val v depth))))))]
      (walk ast 0))))

(defn- check-function-limits
  "Scope-aware per-function limit checking matching PUC-Lua's error_limit format:
   'too many X (limit is Y) in function at line N'
   - Total local variables per function > 200 → 'too many local variables'
   - Distinct upvalue captures per function > 255 → 'too many upvalues'"
  [ast]
  (let [local-limit (long 200)
        upval-limit (long 255)
        func-node? (fn [n] (#{:func-def-stat :local-func-def :global-func-def :function-def}
                            (:type n)))]
    (letfn [;; Extract parameter name strings from a :func-body node
            (param-names [func-body]
              (into #{} (keep :value (get-in func-body [:params :params]))))

            ;; Collect all :name value strings referenced in a value tree,
            ;; NOT recursing into nested function bodies.
            (collect-refs [v]
              (cond
                (map? v)
                (cond
                  (= :name (:type v)) (when (string? (:value v)) [(:value v)])
                  (func-node? v) nil
                  :else (mapcat collect-refs (vals v)))
                (vector? v) (mapcat collect-refs v)
                :else nil))

            ;; Check one function body; recurse into nested function definitions.
            (check-func [func-body func-line outer-scopes]
              (let [params (param-names func-body)
                    block (:body func-body)
                    stmts (filter map? (:statements block))
                    total (atom (count params))
                    locals (atom params)]
                ;; Pass 1: count locals and verify limit
                (doseq [stmt stmts]
                  (case (:type stmt)
                    :local
                    (let [cnt (long (count (get-in stmt [:names :names])))
                          new-tot (unchecked-add (long @total) cnt)]
                      (when (> new-tot local-limit)
                        (throw (ex-info (str "too many local variables"
                                             " (limit is " local-limit
                                             ") in function at line " func-line)
                                        {:type :parse-error})))
                      (reset! total new-tot)
                      (swap! locals into (map :value (get-in stmt [:names :names]))))
                    :local-func-def
                    (do (when (> (unchecked-inc (long @total)) local-limit)
                          (throw (ex-info (str "too many local variables"
                                               " (limit is " local-limit
                                               ") in function at line " func-line)
                                          {:type :parse-error})))
                        (swap! total inc)
                        (swap! locals conj (:value (:name stmt))))
                    nil))
                ;; Pass 2: count upvalues (distinct outer-scope refs)
                (let [all-locals @locals
                      raw-refs (into #{} (keep identity (mapcat collect-refs stmts)))
                      upvals (into #{} (filter (fn [n]
                                                 (and (not (contains? all-locals n))
                                                      (some #(contains? % n) outer-scopes)))
                                               raw-refs))]
                  (when (> (long (count upvals)) upval-limit)
                    (throw (ex-info (str "too many upvalues"
                                         " (limit is " upval-limit
                                         ") in function at line " func-line)
                                    {:type :parse-error}))))
                ;; Pass 3: recurse into nested function definitions
                (let [new-outer (conj outer-scopes @locals)]
                  (doseq [stmt stmts]
                    (if (func-node? stmt)
                      (check-func (:body stmt) (:line stmt) new-outer)
                      (check-inline-funcs stmt new-outer))))))

            ;; Walk a value looking for inline :function-def expressions
            (check-inline-funcs [v outer-scopes]
              (cond
                (map? v)
                (if (func-node? v)
                  (check-func (:body v) (:line v) outer-scopes)
                  (doseq [[k child] v]
                    (when (not= k :type)
                      (check-inline-funcs child outer-scopes))))
                (vector? v) (doseq [item v] (check-inline-funcs item outer-scopes))
                :else nil))]

      ;; Scan chunk-level statements, tracking chunk-level locals.
      ;; Also enforce the local-variable limit at chunk level (main chunk counts too).
      ;; Chunk-level errors use the simple format (no "in function at line N") because
      ;; the main chunk has no defining line, and the testrep tests only check for "too many".
      (let [stmts (filter map? (get-in ast [:body 0 :statements]))
            chunk-locals (atom #{})
            chunk-total (atom 0)]
        (doseq [stmt stmts]
          (case (:type stmt)
            :local
            (let [cnt (long (count (get-in stmt [:names :names])))
                  new-tot (unchecked-add (long @chunk-total) cnt)]
              (when (> new-tot local-limit)
                (throw (ex-info "too many local variables" {:type :parse-error})))
              (reset! chunk-total new-tot)
              (swap! chunk-locals into (map :value (get-in stmt [:names :names]))))
            :local-func-def
            (do (when (> (unchecked-inc (long @chunk-total)) local-limit)
                  (throw (ex-info "too many local variables" {:type :parse-error})))
                (swap! chunk-total inc)
                (swap! chunk-locals conj (:value (:name stmt)))
                (check-func (:body stmt) (:line stmt) [@chunk-locals]))
            (:func-def-stat :global-func-def)
            (check-func (:body stmt) (:line stmt) [@chunk-locals])
            (check-inline-funcs stmt [@chunk-locals])))))))

(def ^:private empty-chunk
  "AST for an empty Lua program (no statements)."
  {:type :chunk :body [{:type :block :statements []}]})

;; ============================================================================
(defn parse-and-transform
  "Parse Lua source and transform to clean AST.

   Uses ANTLR4 parser (27x more memory efficient than legacy Instaparse)."
  [source]
  (binding [*literal-string-table* (atom {})]
    (let [normalized (normalize-line-endings source)
          _ (check-malformed-numbers normalized)
          ;; Parse with ANTLR (comments handled by grammar, sent to HIDDEN channel)
          ;; NullPointerException occurs for empty/comment-only input (ANTLR stop_token is null)
          antlr-tree (try
                       (antlr/parse normalized)
                       (catch NullPointerException _
                         nil))]
      (if (nil? antlr-tree)
        empty-chunk
        (let [;; Transform ANTLR tree to Instaparse-compatible format
              ;; Bind *source* so transform-exp can compute operator line numbers
              insta-format (binding [antlr-transform/*source* normalized]
                             (antlr-transform/transform antlr-tree))
              ;; Transform to final CLua AST
              ;; Note: antlr-transform produces Instaparse-like tree, so we need the same transformation
              ast (apply-ast-transformers insta-format)]
          (check-ast-limits ast)
          (check-function-limits ast)
          (validate-goto-scopes ast)
          (const-check/check! ast)
          ast)))))
