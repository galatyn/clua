(ns clua.interpreter.operators
  "Binary and unary operator handling with metamethod fallback for the Lua interpreter."
  (:require [clojure.string :as str]
            [clua.interpreter.env :as env]
            [clua.interpreter.tables :as tables]
            [clua.interpreter.types :as types])
  (:import (java.math BigInteger)))
(set! *warn-on-reflection* true)


;; Range constants for float-to-integer conversion (Lua 5.3 semantics).
;; Valid long range as doubles: [Long/MIN_VALUE, -(Long/MIN_VALUE)).
;; Note: -(double Long/MIN_VALUE) = 2^63 exactly, which is > Long/MAX_VALUE.
(def ^:const ^:private dbl-min-int (double Long/MIN_VALUE))
(def ^:const ^:private dbl-max-int (- (double Long/MIN_VALUE)))

(defn- lua-int-op
  "Apply an integer arithmetic op with wrapping (Lua 5.3 semantics).
   When both are integers, wraps modulo 2^64. When either is a float, uses float arithmetic."
  [op left-val right-val]
  (let [both-int (and (integer? left-val) (integer? right-val))]
    (case op
      "+" (if both-int
            (unchecked-add (long left-val) (long right-val))
            (+ (double left-val) (double right-val)))
      "-" (if both-int
            (unchecked-subtract (long left-val) (long right-val))
            (- (double left-val) (double right-val)))
      "*" (if both-int
            (unchecked-multiply (long left-val) (long right-val))
            (* (double left-val) (double right-val))))))

(defn- lua-shift
  "Lua 5.3 bitwise shift: shifts >= 64 return 0, negative shifts reverse direction."
  [left-val right-val left?]
  (let [v (long left-val)
        n (long right-val)]
    (cond
      (neg? n) (let [abs-n (unchecked-negate n)]
                 ;; Long.MIN_VALUE negated overflows back to Long.MIN_VALUE (negative).
                 ;; Any shift by |Long.MIN_VALUE| is far >= 64, so the result is 0.
                 (if (neg? abs-n)
                   0
                   (if left?
                     (lua-shift v abs-n false)
                     (lua-shift v abs-n true))))
      (>= n 64) 0
      :else (if left?
              (bit-shift-left v n)
              (unsigned-bit-shift-right v n)))))

(defn- lua-div
  "Lua 5.3 float division (always returns double)."
  [left-val right-val]
  (/ (double left-val) (double right-val)))

(defn- cmp-float-int
  "Compare float f to integer i.
   Returns negative if f<i, 0 if f==i, positive if f>i, nil if f is NaN."
  [f i]
  (let [d (double f) l (long i)]
    (cond
      (Double/isNaN d) nil
      (>= d dbl-max-int) 1                                  ; f >= 2^63 > any signed long
      (< d dbl-min-int) -1                                  ; f < -2^63 < any signed long
      :else
      (let [fi (long (Math/floor d))
            frac? (> d (double fi))]
        (cond
          (< fi l) -1
          (> fi l) 1
          frac? 1                                           ; floor(f)==i but f has fractional part → f > i
          :else 0)))))

(defn- lua-num-cmp
  "Compare two Lua numbers per Lua 5.3 semantics.
   Returns negative/zero/positive, or nil if either operand is NaN."
  [a b]
  (cond
    (and (integer? a) (integer? b)) (Long/compare (long a) (long b))
    (and (float? a) (float? b))
    (let [da (double a) db (double b)]
      (if (or (Double/isNaN da) (Double/isNaN db))
        nil
        ;; Use primitive IEEE 754 comparisons: -0.0 == 0.0 (Double/compare would give -1)
        (cond (== da db) 0
              (< da db) -1
              :else 1)))
    (float? a) (cmp-float-int a (long b))
    :else (let [c (cmp-float-int b (long a))] (when (some? c) (- (long c))))))

(defn- lua-idiv
  "Lua 5.3 integer floor division."
  [left-val right-val]
  (if (and (integer? left-val) (integer? right-val))
    (let [a (long left-val) b (long right-val)]
      (when (zero? b)
        (throw (ex-info "attempt to perform 'n//0' (divide by zero)" {:type :error})))
      (if (and (= a Long/MIN_VALUE) (= b -1))
        Long/MIN_VALUE
        (Math/floorDiv a b)))
    (Math/floor (lua-div left-val right-val))))

(defn- lua-mod-float
  "Lua 5.3 float modulo: equivalent to C's fmod(a,b) + floor adjustment.
   fmod(a,b) is IEEE 754 remainder: a - trunc(a/b)*b.
   Floor adjustment: if result and b have opposite signs, add b.
   Special cases matching PUC-Lua / IEEE 754:
     zero b            → NaN
     NaN in either     → NaN
     Inf in a          → NaN  (fmod(±Inf, y) = NaN for any finite/inf y)
     finite a, ±Inf b  → a, then floor-adjusted if signs differ"
  [^double da ^double db]
  (cond
    (zero? db) Double/NaN
    (Double/isNaN da) Double/NaN
    (Double/isNaN db) Double/NaN
    (Double/isInfinite da) Double/NaN
    (Double/isInfinite db)
    ;; fmod(finite, ±Inf) = da (magnitude of da < Inf), then floor-adjust
    (if (not= (neg? da) (neg? db)) (+ da db) da)
    :else
    ;; Both finite, non-zero db.
    ;; Java % on doubles loses precision for large integer values because the
    ;; intermediate division a/b is rounded and the error accumulates
    ;; (e.g. 2^60 % 3.0 → 0.0 instead of 1.0). C's fmod() avoids this by
    ;; using extended precision internally.
    ;; Fix: when both values are exact integers use BigDecimal (exact arithmetic).
    ;; new BigDecimal(double) gives the exact binary value of the double, so
    ;; BigDecimal(2^60) = 1152921504606846976 exactly.
    (let [m (double
              (if (and (== da (Math/floor da)) (== db (Math/floor db)))
                (-> (java.math.BigDecimal. da)
                    (.remainder (java.math.BigDecimal. db))
                    .doubleValue)
                (rem da db)))]
      (if (and (not (Double/isNaN m)) (not (zero? m))
               (not= (neg? m) (neg? db)))
        (+ m db)
        m))))

(defn- lua-mod
  "Lua 5.3 modulo."
  [left-val right-val]
  (if (and (integer? left-val) (integer? right-val))
    (let [a (long left-val) b (long right-val)]
      (when (zero? b)
        (throw (ex-info "attempt to perform 'n%0'" {:type :error})))
      (Math/floorMod a b))
    (lua-mod-float (double left-val) (double right-val))))

(defn- parse-lua-number-for-bitwise
  "Parse a Lua number string for use in bitwise operations.
   Handles hex integers (0xAA), hex floats without P exponent (0xAA.0),
   hex floats with P exponent (0x1.8p+1), and decimal numbers.
   Locale-aware: respects the current numeric locale's decimal separator.
   Returns a Java Number or nil."
  [s]
  (let [trimmed (str/trim s)
        dec-char (env/numeric-decimal-char env/*current-env*)]
    (try
      (if (re-matches #"(?i)[+-]?0x.*" trimmed)
        ;; Hex number: check for fractional part using "." or locale decimal char
        (let [has-frac (or (str/includes? trimmed ".")
                           (str/includes? trimmed (str dec-char)))]
          (if has-frac
            ;; Hex float - normalize locale decimal to ".", add p0 if no exponent
            (let [normalized (if (= dec-char \.)
                               trimmed
                               (str/replace trimmed (str dec-char) "."))
                  float-str (if (re-find #"(?i)p" normalized)
                              normalized
                              (str normalized "p0"))]
              (Double/parseDouble float-str))
            ;; Hex integer - parse via BigInteger to handle overflow
            (let [negative? (str/starts-with? trimmed "-")
                  abs-str (if (or negative? (str/starts-with? trimmed "+"))
                            (subs trimmed 1)
                            trimmed)
                  hex-digits (subs abs-str 2)
                  mag (BigInteger. hex-digits 16)]
              (.longValue (if negative? (.negate mag) mag)))))
        ;; Decimal number - locale-aware: normalize decimal separator, try long then double
        (try (Long/parseLong trimmed)
             (catch NumberFormatException _
               (let [normalized (if (= dec-char \.)
                                  trimmed
                                  (str/replace trimmed (str dec-char) "."))]
                 (Double/parseDouble normalized)))))
      (catch Exception _ nil))))

(defn- float->long-if-exact
  "Convert a double to long if it is finite and representable as a signed 64-bit integer.
   Returns nil otherwise."
  [^double d]
  (when (and (>= d dbl-min-int) (< d dbl-max-int))
    (let [l (long d)]
      (when (== d (double l)) l))))

(defn coerce-arith
  "Coerce a value to a Lua number for arithmetic (string→number conversion).
   Returns the number if v is already a number, parses v if it is a numeric string,
   or returns nil if coercion is not possible."
  [v]
  (cond
    (number? v) v
    (string? v) (parse-lua-number-for-bitwise v)
    :else nil))

(defn coerce-bitwise
  "Coerce a value to an integer for bitwise operations per Lua 5.3 rules.
   Integers pass through. Floats with exact integer value are converted to long.
   Strings are parsed as Lua numbers and then checked for integer value.
   Returns nil if coercion is not possible."
  [v]
  (cond
    (integer? v) (if (instance? BigInteger v) (.longValue ^BigInteger v) v)
    (float? v) (float->long-if-exact (double v))
    (string? v) (let [n (parse-lua-number-for-bitwise v)]
                  (cond
                    (nil? n) nil
                    (integer? n) (if (instance? BigInteger n) (.longValue ^BigInteger n) n)
                    (float? n) (float->long-if-exact (double n))
                    :else nil))
    :else nil))

(defn bitwise-type-name
  "Return the Lua type name of a value for arithmetic/bitwise error messages.
   Delegates to tables/lua-type-name so __name in metatable is respected."
  [v]
  (cond
    (nil? v) "nil"
    (boolean? v) "boolean"
    (number? v) "number"
    (string? v) "string"
    :else (tables/lua-type-name v)))

(defn- lua-type-name
  "Return the Lua type name of a value for error messages.
   Delegates to tables/lua-type-name so __name in metatable is respected."
  [v]
  (tables/lua-type-name v))

(defn- throw-compare-error
  "Throw a Lua 'attempt to compare' error for incompatible types."
  [left right]
  (let [lt (lua-type-name left)
        rt (lua-type-name right)]
    (throw (ex-info (if (= lt rt)
                      (str "attempt to compare two " lt " values")
                      (str "attempt to compare " lt " with " rt))
                    {:type :error}))))

(defn bitwise-error-msg
  "Return the appropriate error message when bitwise coercion fails for value v.
   Numbers that lack an integer representation get a specific message."
  [v]
  (if (number? v)
    "number has no integer representation"
    (str "attempt to perform bitwise operation on a " (bitwise-type-name v) " value")))

(defn apply-binary-op
  "Apply a binary operator with metamethod fallback."
  [op left-val right-val env]
  (let [both-numbers (and (number? left-val) (number? right-val))
        both-strings (and (string? left-val) (string? right-val))
        bw-left (coerce-bitwise left-val)
        bw-right (coerce-bitwise right-val)]
    (case op
      "+" (if both-numbers
            (lua-int-op op left-val right-val)
            (let [l (coerce-arith left-val) r (coerce-arith right-val)]
              (if (and l r)
                (lua-int-op op l r)
                (or (tables/try-binary-metamethod op left-val right-val env)
                    (throw (ex-info (str "attempt to perform arithmetic on a "
                                         (bitwise-type-name (if (nil? l) left-val right-val)) " value")
                                    {:type :error}))))))
      "-" (if both-numbers
            (lua-int-op op left-val right-val)
            (let [l (coerce-arith left-val) r (coerce-arith right-val)]
              (if (and l r)
                (lua-int-op op l r)
                (or (tables/try-binary-metamethod op left-val right-val env)
                    (throw (ex-info (str "attempt to perform arithmetic on a "
                                         (bitwise-type-name (if (nil? l) left-val right-val)) " value")
                                    {:type :error}))))))
      "*" (if both-numbers
            (lua-int-op op left-val right-val)
            (let [l (coerce-arith left-val) r (coerce-arith right-val)]
              (if (and l r)
                (lua-int-op op l r)
                (or (tables/try-binary-metamethod op left-val right-val env)
                    (throw (ex-info (str "attempt to perform arithmetic on a "
                                         (bitwise-type-name (if (nil? l) left-val right-val)) " value")
                                    {:type :error}))))))
      "/" (if both-numbers
            (lua-div left-val right-val)
            (let [l (coerce-arith left-val) r (coerce-arith right-val)]
              (if (and l r)
                (lua-div l r)
                (or (tables/try-binary-metamethod op left-val right-val env)
                    (throw (ex-info (str "attempt to perform arithmetic on a "
                                         (bitwise-type-name (if (nil? l) left-val right-val)) " value")
                                    {:type :error}))))))
      "//" (if both-numbers
             (lua-idiv left-val right-val)
             (let [l (coerce-arith left-val) r (coerce-arith right-val)]
               (if (and l r)
                 (lua-idiv l r)
                 (or (tables/try-binary-metamethod op left-val right-val env)
                     (throw (ex-info (str "attempt to perform arithmetic on a "
                                          (bitwise-type-name (if (nil? l) left-val right-val)) " value")
                                     {:type :error}))))))
      "%" (if both-numbers
            (lua-mod left-val right-val)
            (let [l (coerce-arith left-val) r (coerce-arith right-val)]
              (if (and l r)
                (lua-mod l r)
                (or (tables/try-binary-metamethod op left-val right-val env)
                    (throw (ex-info (str "attempt to perform arithmetic on a "
                                         (bitwise-type-name (if (nil? l) left-val right-val)) " value")
                                    {:type :error}))))))
      "^" (if both-numbers
            (Math/pow (double left-val) (double right-val))
            (let [l (coerce-arith left-val) r (coerce-arith right-val)]
              (if (and l r)
                (Math/pow (double l) (double r))
                (or (tables/try-binary-metamethod op left-val right-val env)
                    (throw (ex-info (str "attempt to perform arithmetic on a "
                                         (bitwise-type-name (if (nil? l) left-val right-val)) " value")
                                    {:type :error}))))))
      ".." (if (or both-strings both-numbers
                   (and (string? left-val) (number? right-val))
                   (and (number? left-val) (string? right-val)))
             (let [result (str left-val right-val)]
               (env/track-allocation! env (+ 48 (* 2 (count result))))
               result)
             (or (tables/try-binary-metamethod op left-val right-val env)
                 (let [bad-val (if (not (or (string? left-val) (number? left-val)))
                                 left-val
                                 right-val)]
                   (throw (ex-info (str "attempt to concatenate a "
                                        (lua-type-name bad-val) " value")
                                   {:type :error})))))
      "==" (if both-numbers
             (= 0 (lua-num-cmp left-val right-val))
             (let [[found result] (tables/try-comparison-metamethod op left-val right-val env)]
               (if found result (= left-val right-val))))
      "~=" (if both-numbers
             (not= 0 (lua-num-cmp left-val right-val))
             (let [[found result] (tables/try-comparison-metamethod op left-val right-val env)]
               (if found result (not= left-val right-val))))
      "<" (if both-numbers
            (let [c (lua-num-cmp left-val right-val)]
              (and (some? c) (neg? (long c))))
            (if both-strings
              (neg? (.compareTo ^String left-val ^String right-val))
              (let [[found result] (tables/try-comparison-metamethod op left-val right-val env)]
                (if found result (throw-compare-error left-val right-val)))))
      "<=" (if both-numbers
             (let [c (lua-num-cmp left-val right-val)]
               (and (some? c) (not (pos? (long c)))))
             (if both-strings
               (not (pos? (.compareTo ^String left-val ^String right-val)))
               (let [[found result] (tables/try-comparison-metamethod op left-val right-val env)]
                 (if found result (throw-compare-error left-val right-val)))))
      ">" (if both-numbers
            (let [c (lua-num-cmp left-val right-val)]
              (and (some? c) (pos? (long c))))
            (if both-strings
              (pos? (.compareTo ^String left-val ^String right-val))
              (let [[found result] (tables/try-comparison-metamethod op left-val right-val env)]
                (if found result (throw-compare-error left-val right-val)))))
      ">=" (if both-numbers
             (let [c (lua-num-cmp left-val right-val)]
               (and (some? c) (not (neg? (long c)))))
             (if both-strings
               (not (neg? (.compareTo ^String left-val ^String right-val)))
               (let [[found result] (tables/try-comparison-metamethod op left-val right-val env)]
                 (if found result (throw-compare-error left-val right-val)))))
      "&" (if (and bw-left bw-right)
            (bit-and (long bw-left) (long bw-right))
            (or (tables/try-binary-metamethod op left-val right-val env)
                (throw (ex-info (bitwise-error-msg (if (nil? bw-left) left-val right-val))
                                {:type :error}))))
      "|" (if (and bw-left bw-right)
            (bit-or (long bw-left) (long bw-right))
            (or (tables/try-binary-metamethod op left-val right-val env)
                (throw (ex-info (bitwise-error-msg (if (nil? bw-left) left-val right-val))
                                {:type :error}))))
      "~" (if (and bw-left bw-right)
            (bit-xor (long bw-left) (long bw-right))
            (or (tables/try-binary-metamethod op left-val right-val env)
                (throw (ex-info (bitwise-error-msg (if (nil? bw-left) left-val right-val))
                                {:type :error}))))
      "<<" (if (and bw-left bw-right)
             (lua-shift (long bw-left) (long bw-right) true)
             (or (tables/try-binary-metamethod op left-val right-val env)
                 (throw (ex-info (bitwise-error-msg (if (nil? bw-left) left-val right-val))
                                 {:type :error}))))
      ">>" (if (and bw-left bw-right)
             (lua-shift (long bw-left) (long bw-right) false)
             (or (tables/try-binary-metamethod op left-val right-val env)
                 (throw (ex-info (bitwise-error-msg (if (nil? bw-left) left-val right-val))
                                 {:type :error})))))))

;; Post-process helpers for metamethod results.
;; These are used by find-binary-metamethod and find-unary-metamethod to convert
;; a raw metamethod return value into the expected operation result.
(defn- mm-unwrap [r] (if (vector? r) (first r) r))
(defn- mm-truthy [r] (types/lua-truthy? (mm-unwrap r)))
(defn- mm-not-truthy [r] (not (mm-truthy r)))

(defn find-binary-metamethod
  "Detect whether a binary operation needs a metamethod call.
   Returns nil if the operation can proceed without a metamethod (primitives are fine,
   or for == no matching __eq exists).
   Returns {:fn mm :args [...] :post-process fn} if a metamethod must be called.
   Throws with {:type :error} if operand types are incompatible and no metamethod exists."
  [op left right]
  (let [mm-name (tables/binary-metamethods op)]
    (case op
      ("and" "or") nil
      ;; Arithmetic: coercible to number → direct; else metamethod or error
      ("+" "-" "*" "/" "//" "%" "^")
      (when-not (and (some? (coerce-arith left)) (some? (coerce-arith right)))
        (if-let [mm (when mm-name (or (tables/get-metamethod left mm-name)
                                      (tables/get-metamethod right mm-name)))]
          {:fn mm :args [left right] :post-process mm-unwrap}
          (throw (ex-info (str "attempt to perform arithmetic on a "
                               (bitwise-type-name (if (nil? (coerce-arith left)) left right)) " value")
                          {:type :error}))))
      ;; Concat: string/number coercible → direct; else metamethod or error
      ".." (when-not (and (or (string? left) (number? left))
                          (or (string? right) (number? right)))
             (if-let [mm (or (tables/get-metamethod left "__concat")
                             (tables/get-metamethod right "__concat"))]
               {:fn mm :args [left right] :post-process mm-unwrap}
               (throw (ex-info (str "attempt to concatenate a "
                                    (lua-type-name (if-not (or (string? left) (number? left)) left right)) " value")
                               {:type :error}))))
      ;; Bitwise: coercible to integer → direct; else metamethod or error
      ("&" "|" "~" "<<" ">>")
      (let [bw-left (coerce-bitwise left)
            bw-right (coerce-bitwise right)]
        (when-not (and (some? bw-left) (some? bw-right))
          (if-let [mm (when mm-name (or (tables/get-metamethod left mm-name)
                                        (tables/get-metamethod right mm-name)))]
            {:fn mm :args [left right] :post-process mm-unwrap}
            (throw (ex-info (bitwise-error-msg (if (nil? bw-left) left right))
                            {:type :error})))))
      ;; Comparisons: both numbers or both strings → direct; else metamethod or error
      "<" (when-not (or (and (number? left) (number? right))
                        (and (string? left) (string? right)))
            (if-let [mm (or (tables/get-metamethod left "__lt")
                            (tables/get-metamethod right "__lt"))]
              {:fn mm :args [left right] :post-process mm-truthy}
              (throw-compare-error left right)))
      "<=" (when-not (or (and (number? left) (number? right))
                         (and (string? left) (string? right)))
             (or (when-let [mm (or (tables/get-metamethod left "__le")
                                   (tables/get-metamethod right "__le"))]
                   {:fn mm :args [left right] :post-process mm-truthy})
                 (when-let [mm (or (tables/get-metamethod left "__lt")
                                   (tables/get-metamethod right "__lt"))]
                   {:fn mm :args [right left] :post-process mm-not-truthy})
                 (throw-compare-error left right)))
      ">" (when-not (or (and (number? left) (number? right))
                        (and (string? left) (string? right)))
            (if-let [mm (or (tables/get-metamethod right "__lt")
                            (tables/get-metamethod left "__lt"))]
              {:fn mm :args [right left] :post-process mm-truthy}
              (throw-compare-error left right)))
      ">=" (when-not (or (and (number? left) (number? right))
                         (and (string? left) (string? right)))
             (or (when-let [mm (or (tables/get-metamethod right "__le")
                                   (tables/get-metamethod left "__le"))]
                   {:fn mm :args [right left] :post-process mm-truthy})
                 (when-let [mm (or (tables/get-metamethod right "__lt")
                                   (tables/get-metamethod left "__lt"))]
                   {:fn mm :args [left right] :post-process mm-not-truthy})
                 (throw-compare-error left right)))
      ;; Equality (Lua 5.3): try __eq from either operand; skip if primitively equal
      "==" (when-not (or (and (number? left) (number? right))
                         (identical? left right))
             (let [mm (or (tables/get-metamethod left "__eq")
                          (tables/get-metamethod right "__eq"))]
               (when mm {:fn mm :args [left right] :post-process mm-truthy})))
      "~=" (when-not (or (and (number? left) (number? right))
                         (identical? left right))
             (let [mm (or (tables/get-metamethod left "__eq")
                          (tables/get-metamethod right "__eq"))]
               (when mm {:fn mm :args [left right] :post-process mm-not-truthy})))
      ;; Unknown op: let apply-binary-op handle it
      nil)))

(defn find-unary-metamethod
  "Detect whether a unary operation needs a metamethod call.
   Returns nil if the operation can proceed without a metamethod.
   Returns {:fn mm :args [...] :post-process fn} if a metamethod must be called.
   Throws with {:type :error} if the operand type is incompatible and no metamethod exists."
  [op val]
  (case op
    "not" nil
    ;; Unary minus: numeric/coercible → direct; else __unm or error
    ;; Per Lua spec, __unm is called with the operand passed twice: __unm(val, val)
    "-" (when-not (or (number? val) (some? (coerce-arith val)))
          (if-let [mm (tables/get-metamethod val "__unm")]
            {:fn mm :args [val val] :post-process mm-unwrap}
            (throw (ex-info (str "attempt to perform arithmetic on a "
                                 (bitwise-type-name val) " value")
                            {:type :error}))))
    ;; Length: string → direct; table with __len → metamethod; table without → direct;
    ;; basic type with type-level __len → metamethod; else error
    ;; Per Lua spec, __len is called with the operand passed twice: __len(val, val)
    "#" (cond
          (types/lua-table? val)
          (when-let [mm (tables/get-metamethod val "__len")]
            {:fn mm :args [val val] :post-process mm-unwrap})
          (string? val) nil
          :else
          (if-let [mm (tables/get-metamethod val "__len")]
            {:fn mm :args [val val] :post-process mm-unwrap}
            (throw (ex-info (str "attempt to get length of a " (lua-type-name val) " value")
                            {:type :error}))))
    ;; Bitwise not: integer-coercible → direct; else __bnot or error
    ;; Per Lua spec, __bnot is called with the operand passed twice: __bnot(val, val)
    "~" (when-not (some? (coerce-bitwise val))
          (if-let [mm (tables/get-metamethod val "__bnot")]
            {:fn mm :args [val val] :post-process mm-unwrap}
            (throw (ex-info (bitwise-error-msg val) {:type :error}))))))
