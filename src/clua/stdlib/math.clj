(ns clua.stdlib.math
  "Lua math library implementation.

   Implements Lua 5.3 math functions.
   All trigonometric functions work in radians."
  (:require [clojure.string :as str]
            [clua.interpreter.env :as env]
            [clua.interpreter.tables :as tables]
            [clua.stdlib.xoshiro256 :as xoshiro]))
(set! *warn-on-reflection* true)
(set! *unchecked-math* :warn-on-boxed)


;; =============================================================================
;; Basic Math Functions
;; =============================================================================

;; Range constants for float-to-integer conversion (mirrors operators.clj).
;; Valid long range as doubles: [Long/MIN_VALUE, -(Long/MIN_VALUE)).
(def ^:private ^:const dbl-min-int (double Long/MIN_VALUE))
(def ^:private ^:const dbl-max-int (- (double Long/MIN_VALUE)))

(defn- double->long-if-representable
  "Convert double d to long if it is finite and exactly representable as a signed 64-bit int.
   Returns the long, or d unchanged if conversion is not possible."
  [^double d]
  (if (and (>= d dbl-min-int) (< d dbl-max-int))
    (let [l (long d)]
      (if (== d (double l)) l d))
    d))

(defn lua-abs
  "math.abs(x) - Returns the absolute value of x. Preserves integer type."
  [x]
  (if (integer? x)
    (Math/abs (long x))
    (Math/abs (double x))))

(defn lua-ceil
  "math.ceil(x) - Returns the smallest integer >= x. Returns long when result fits."
  [x]
  (when-not (number? x)
    (throw (ex-info "bad argument #1 to 'ceil' (number expected)" {:type :error})))
  (if (integer? x)
    (long x)
    (double->long-if-representable (Math/ceil (double x)))))

(defn lua-floor
  "math.floor(x) - Returns the largest integer <= x. Returns long when result fits."
  [x]
  (when-not (number? x)
    (throw (ex-info "bad argument #1 to 'floor' (number expected)" {:type :error})))
  (if (integer? x)
    (long x)
    (double->long-if-representable (Math/floor (double x)))))

(defn lua-max
  "math.max(x, ...) - Returns the maximum value among arguments."
  [& args]
  (if (empty? args)
    (throw (ex-info "bad argument #1 to 'max' (value expected)" {:type :error}))
    (apply max args)))

(defn lua-min
  "math.min(x, ...) - Returns the minimum value among arguments."
  [& args]
  (if (empty? args)
    (throw (ex-info "bad argument #1 to 'min' (value expected)" {:type :error}))
    (apply min args)))

(defn lua-sqrt
  "math.sqrt(x) - Returns the square root of x."
  [x]
  (Math/sqrt (double x)))

(defn lua-pow
  "math.pow(x, y) - Returns x raised to the power y.
   Note: In Lua 5.3+, this is deprecated in favor of x^y operator."
  [x y]
  (Math/pow (double x) (double y)))

(defn lua-exp
  "math.exp(x) - Returns e^x."
  [x]
  (Math/exp (double x)))

(defn lua-log
  "math.log(x [, base]) - Returns logarithm of x.
   If base is given, returns log_base(x), otherwise returns natural log."
  [x & [base]]
  (if base
    (/ (Math/log (double x)) (Math/log (double base)))
    (Math/log (double x))))

;; =============================================================================
;; Trigonometric Functions
;; =============================================================================

(defn- check-number-arg
  "Throw a Lua-style type error if v is not a number."
  [v arg-n fname]
  (when-not (number? v)
    (throw (ex-info (str "bad argument #" arg-n " to '" fname
                         "' (number expected, got " (tables/lua-type-name v) ")")
                    {:type :error}))))

(defn lua-sin
  "math.sin(x) - Returns the sine of x (in radians)."
  [x]
  (check-number-arg x 1 "sin")
  (Math/sin (double x)))

(defn lua-cos
  "math.cos(x) - Returns the cosine of x (in radians)."
  [x]
  (check-number-arg x 1 "cos")
  (Math/cos (double x)))

(defn lua-tan
  "math.tan(x) - Returns the tangent of x (in radians)."
  [x]
  (check-number-arg x 1 "tan")
  (Math/tan (double x)))

(defn lua-asin
  "math.asin(x) - Returns the arc sine of x (in radians)."
  [x]
  (check-number-arg x 1 "asin")
  (Math/asin (double x)))

(defn lua-acos
  "math.acos(x) - Returns the arc cosine of x (in radians)."
  [x]
  (check-number-arg x 1 "acos")
  (Math/acos (double x)))

(defn lua-atan
  "math.atan(y [, x]) - Returns the arc tangent of y/x (in radians).
   Uses the signs of both arguments to find the quadrant of the result.
   If x is omitted, returns atan(y)."
  [y & [x]]
  (check-number-arg y 1 "atan")
  (if x
    (Math/atan2 (double y) (double x))
    (Math/atan (double y))))

;; =============================================================================
;; Hyperbolic Functions (Lua 5.3 removed these, but we include them)
;; =============================================================================

(defn lua-sinh
  "math.sinh(x) - Returns the hyperbolic sine of x."
  [x]
  (Math/sinh (double x)))

(defn lua-cosh
  "math.cosh(x) - Returns the hyperbolic cosine of x."
  [x]
  (Math/cosh (double x)))

(defn lua-tanh
  "math.tanh(x) - Returns the hyperbolic tangent of x."
  [x]
  (Math/tanh (double x)))

;; =============================================================================
;; Angle Conversion
;; =============================================================================

(defn lua-deg
  "math.deg(x) - Converts x from radians to degrees."
  [x]
  (Math/toDegrees (double x)))

(defn lua-rad
  "math.rad(x) - Converts x from degrees to radians."
  [x]
  (Math/toRadians (double x)))

;; =============================================================================
;; Rounding and Remainder Functions
;; =============================================================================

(defn- truncate
  "Truncates towards zero (rounds towards zero)."
  ^double [^double x]
  (if (neg? x)
    (Math/ceil x)
    (Math/floor x)))

(defn lua-modf
  "math.modf(x) - Returns the integral and fractional parts of x.
   Integer input returns [integer, 0.0]. Float input returns [float-trunc, float-frac].
   ±Inf returns [±Inf, 0.0]. NaN returns [NaN, NaN]."
  [x]
  (if (integer? x)
    [(long x) 0.0]
    (let [d (double x)]
      (if (Double/isInfinite d)
        [d 0.0]
        (let [int-part (truncate d)
              frac-part (- d int-part)]
          [int-part frac-part])))))

(defn lua-fmod
  "math.fmod(x, y) - Returns the remainder of x/y that rounds towards zero.
   Integer inputs return an integer result; float inputs return a float."
  [x y]
  (if (and (integer? x) (integer? y))
    (let [a (long x) b (long y)]
      (when (zero? b)
        (throw (ex-info "bad argument #2 to 'fmod' (zero)" {:type :error})))
      (rem a b))
    (let [xd (double x) yd (double y)]
      (- xd (* yd (truncate (/ xd yd)))))))

;; =============================================================================
;; frexp / ldexp (reintroduced in Lua 5.5)
;; =============================================================================

(defn lua-frexp
  "math.frexp(x) - Decompose x into mantissa m and exponent p such that
   x = m * 2^p, with 0.5 <= |m| < 1 (or m = x for 0 / Inf / NaN).
   Returns two values: m (float), p (integer)."
  [x]
  (let [d (double x)]
    (cond
      (zero? d) [0.0 0]
      (Double/isInfinite d) [d 0]
      (Double/isNaN d) [d 0]
      :else
      (let [p (int (+ (Math/getExponent d) 1))
            m (Math/scalb ^double d (int (- p)))]
        [m (long p)]))))

(defn lua-ldexp
  "math.ldexp(m, p) - Return m * 2^p (p must be an integer)."
  [m p]
  (Math/scalb ^double (double m) (int (long p))))

;; =============================================================================
;; Integer Functions (Lua 5.3+)
;; =============================================================================

(defn- float->long-exact
  "Returns the long value of d if d is an exact signed 64-bit integer, else nil."
  [^double d]
  (when (and (>= d dbl-min-int) (< d dbl-max-int))
    (let [l (long d)]
      (when (== d (double l)) l))))

(defn- parse-tointeger-str
  "Parse a numeric string and return its integer value if it represents an exact integer, else nil."
  [s]
  (let [trimmed (str/trim s)]
    (when (seq trimmed)
      (try
        (if (re-matches #"(?i)[+-]?0x[0-9a-f]+" trimmed)
          ;; Hex integer
          (let [neg? (str/starts-with? trimmed "-")
                abs-str (if (or neg? (str/starts-with? trimmed "+")) (subs trimmed 1) trimmed)
                mag (BigInteger. (subs abs-str 2) 16)]
            (.longValue (if neg? (.negate mag) mag)))
          ;; Try Long directly (handles decimal integers including minint/maxint)
          (try (Long/parseLong trimmed)
               (catch NumberFormatException _
                 ;; Try Double (handles "34.0", "3e0", etc.)
                 (try (float->long-exact (Double/parseDouble trimmed))
                      (catch NumberFormatException _ nil)))))
        (catch Exception _ nil)))))

(defn lua-tointeger
  "math.tointeger(x) - Converts x to an integer if possible, otherwise returns nil.
   Accepts numbers and numeric strings."
  [x]
  (cond
    (integer? x) (long x)
    (float? x) (float->long-exact (double x))
    (string? x) (parse-tointeger-str x)
    :else nil))

(defn lua-type
  "math.type(x) - Returns 'integer' if x is an integer, 'float' if it is a float,
   or nil if x is not a number. In Lua 5.3, 1.0 is always 'float', 1 is 'integer'."
  [x]
  (cond
    (not (number? x)) nil
    (float? x) "float"
    (integer? x) "integer"
    ;; For other number types (Ratio, BigDecimal, etc.), treat as float
    :else "float"))

(defn lua-ult
  "math.ult(m, n) - Returns true if m < n when compared as unsigned integers."
  [m n]
  (let [m (long m)
        n (long n)]
    ;; Java doesn't have unsigned comparison, so we use this trick:
    ;; For unsigned comparison, flip the sign bit and do signed comparison
    (< (unchecked-add m Long/MIN_VALUE) (unchecked-add n Long/MIN_VALUE))))

;; =============================================================================
;; Random Number Functions
;; =============================================================================

(defn lua-random
  "math.random([m [, n]]) - Returns a pseudo-random number.
   Without arguments: returns a float in [0, 1).
   With one argument m: returns an integer in [1, m] (or full range if m=0).
   With two arguments m, n: returns an integer in [m, n].
   Uses xoshiro256** PRNG (matches Lua 5.5 exactly)."
  [& args]
  (let [^longs state (:rng env/*current-env*)]
    (case (count args)
      0 (xoshiro/next-double state)
      1 (let [m (long (first args))]
          (cond
            (zero? m) (xoshiro/next-long state)
            (neg? m) (throw (ex-info "bad argument #1 to 'random' (interval is empty)" {:type :error}))
            :else (unchecked-inc (xoshiro/next-long-in state (unchecked-dec m)))))
      2 (let [m (long (first args))
              n (long (second args))]
          (when (> m n)
            (throw (ex-info "bad argument #2 to 'random' (interval is empty)" {:type :error})))
          (let [diff (unchecked-subtract n m)]
            (if (neg? diff)
              ;; Interval spans more than Long/MAX_VALUE values (unsigned diff overflowed).
              ;; Use rejection sampling — almost all values will be in [m, n].
              (loop []
                (let [r (xoshiro/next-long state)]
                  (if (and (<= m r) (<= r n))
                    r
                    (recur))))
              (unchecked-add m (xoshiro/next-long-in state diff)))))
      (throw (ex-info "wrong number of arguments" {:type :error})))))

(defn lua-randomseed
  "math.randomseed([x [, y]]) - Sets the seed for the random number generator.
   Lua 5.5: seeds xoshiro256** with (x, y); default y = 0.
   With no arguments, uses current time as seed.
   Returns (x, y) — the two seed components used."
  [& args]
  (let [^longs state (:rng env/*current-env*)
        [x y] (case (count args)
                0 [(System/currentTimeMillis) 0]
                1 [(long (first args)) 0]
                2 [(long (first args)) (long (second args))]
                (throw (ex-info "wrong number of arguments to 'randomseed'" {:type :error})))]
    (xoshiro/seed! state x y)
    [x y]))

;; =============================================================================
;; Constants
;; =============================================================================

(def lua-pi
  "math.pi - The value of pi."
  Math/PI)

(def lua-huge
  "math.huge - A value larger than any other numeric value (positive infinity)."
  Double/POSITIVE_INFINITY)

(def lua-max-integer
  "math.maxinteger - Maximum value for an integer."
  Long/MAX_VALUE)

(def lua-min-integer
  "math.mininteger - Minimum value for an integer."
  Long/MIN_VALUE)

;; =============================================================================
;; Export as Lua library table
;; =============================================================================

(def math-lib
  "The complete math library for Lua."
  {;; Basic functions
   "abs" lua-abs
   "ceil" lua-ceil
   "floor" lua-floor
   "max" lua-max
   "min" lua-min
   "sqrt" lua-sqrt
   "pow" lua-pow                                            ; Deprecated in Lua 5.3 but still available
   "exp" lua-exp
   "log" lua-log

   ;; Trigonometric
   "sin" lua-sin
   "cos" lua-cos
   "tan" lua-tan
   "asin" lua-asin
   "acos" lua-acos
   "atan" lua-atan

   ;; Hyperbolic (removed in Lua 5.3 but we keep them)
   "sinh" lua-sinh
   "cosh" lua-cosh
   "tanh" lua-tanh

   ;; Angle conversion
   "deg" lua-deg
   "rad" lua-rad

   ;; Rounding and remainder
   "modf" lua-modf
   "fmod" lua-fmod

   ;; Float decomposition (Lua 5.5, reintroduced from Lua 5.2)
   "frexp" lua-frexp
   "ldexp" lua-ldexp

   ;; Integer functions (Lua 5.3+)
   "tointeger" lua-tointeger
   "type" lua-type
   "ult" lua-ult

   ;; Random
   "random" lua-random
   "randomseed" lua-randomseed                              ; Lua 5.4: returns (x, y) seed state

   ;; Constants
   "pi" lua-pi
   "huge" lua-huge
   "maxinteger" lua-max-integer
   "mininteger" lua-min-integer})
