(ns clua.interpreter.tables
  "Table operations, metatables, and metamethod handling for the Lua interpreter."
  (:require [clua.interpreter.env :as env]
            [clua.interpreter.types :as types])
  (:import (clojure.lang ExceptionInfo)
           (java.util ArrayList HashMap)))

(set! *warn-on-reflection* true)

;; Forward declaration for call-function (defined in core)
(declare call-function)

;; Wrapper for Clojure map keys (Lua functions/tables) stored in Java HashMaps.
;; Uses identity-based hashCode/equals to avoid recursive content hashing of
;; function closures, which causes StackOverflowError on deep environments.
(deftype IdentityMapKey [m]
  Object
  (hashCode [_] (System/identityHashCode m))
  (equals [_this other]
    (and (instance? IdentityMapKey other)
         (identical? m (.m ^IdentityMapKey other)))))

;;; Table operations

(defn make-table
  "Create a new Lua table using Java HashMap and ArrayList for performance.
   Tracks memory allocation against the environment limit."
  ([] (make-table nil))
  ([env]
   (when env (env/track-allocation! env 256))               ; Base table cost
   {:type :lua-table
    :data (java.util.HashMap.)                              ; Mutable HashMap for key-value pairs
    :array (java.util.ArrayList.)                           ; Mutable ArrayList for array part
    :metatable (object-array [nil])}))

;; Range bounds for float-to-integer key normalization.
;; Valid long range as doubles: [Long/MIN_VALUE, -(Long/MIN_VALUE)).
(def ^:const ^:private norm-min (double Long/MIN_VALUE))
(def ^:const ^:private norm-max (- (double Long/MIN_VALUE)))

(defn normalize-key
  "Normalize a Lua table key for storage in the Java HashMap.
   Float keys with no fractional part (including -0.0) are converted to Long.
   Clojure map keys (Lua functions/tables) are wrapped in IdentityMapKey to
   use identity-based hashing/equality, avoiding recursive hash computation.
   Other keys pass through unchanged."
  [key]
  (cond
    (float? key)
    (let [d (double key)]
      (if (and (not (Double/isNaN d))
               (not (Double/isInfinite d))
               (>= d norm-min)
               (< d norm-max)
               (zero? (- d (Math/floor d))))
        (long d)
        key))
    (map? key) (IdentityMapKey. key)
    :else key))

(defn denormalize-key
  "Unwrap a normalized table key back to its original Lua value.
   IdentityMapKey wrappers are unwrapped to the underlying Clojure map.
   Other keys pass through unchanged."
  [key]
  (if (instance? IdentityMapKey key)
    (.m ^IdentityMapKey key)
    key))

(defn- integer-array-key?
  "Returns true if key is a positive integer-valued number fitting in array range.
   In Lua 5.3, only integer-valued floats (e.g. 2.0) are treated as integer keys;
   non-integer floats (e.g. 24.5) are hash keys."
  [key]
  (and (number? key)
       (let [d (double key)]
         (and (pos? d)
              (<= d Integer/MAX_VALUE)
              (let [k (long d)]
                (== d (double k)))))))

(defn table-get
  "Get a value from a Lua table without invoking metamethods.
   Uses 1-based indexing for array part (positive integer-valued keys),
   hash table for all other keys. Falls through to hash when key is in
   integer range but not present in array (handles sparsity).
   Float keys are normalized to integers when they represent exact integers."
  [table key]
  (let [key (normalize-key key)]
    (if (integer-array-key? key)
      ;; Array access - ArrayList uses 0-based indexing
      (let [idx (unchecked-int (dec (long key)))
            ^ArrayList arr (:array table)]
        (if (< idx (.size arr))
          (.get arr idx)
          ;; Not in array - check hash (may have been stored there due to sparsity)
          (.get ^HashMap (:data table) key)))
      ;; Hash access - HashMap (includes float keys, negative keys, strings, etc.)
      (.get ^HashMap (:data table) key))))

(defn table-set!
  "Set a value in a Lua table. Optionally tracks memory allocation."
  ([table key value] (table-set! table key value nil))
  ([table key value env]
   (when (nil? key)
     (throw (ex-info "table index is nil" {:type :error})))
   (when (and (float? key) (Double/isNaN (double key)))
     (throw (ex-info "table index is NaN" {:type :error})))
   (let [key (normalize-key key)]
     (if (integer-array-key? key)
       ;; Integer key in array range
       (let [idx (dec (long key))
             ^ArrayList arr (:array table)
             ^HashMap data (:data table)
             old-size (.size arr)]
         (if (> (- idx old-size) 1024)
           ;; Too sparse: avoid huge array allocation, store in hash instead
           (if (nil? value)
             (.remove data key)
             (.put data key value))
           ;; Normal array path: grow array as needed and set value
           (let [idx-int (unchecked-int idx)]
             (when (and env (>= idx old-size))
               ;; Track memory for array growth (new slots + value)
               (env/track-allocation! env (* 24 (- (inc idx) old-size))))
             (while (> idx (.size arr))
               (.add arr nil))
             (if (= idx (.size arr))
               (.add arr value)
               (.set arr idx-int value)))))
       ;; Hash part - use HashMap (includes keys > Integer/MAX_VALUE)
       (let [^HashMap data (:data table)]
         (if (nil? value)
           ;; Setting to nil removes the key from table
           (.remove data key)
           (do
             (when (and env (not (.containsKey data key)))
               ;; Track memory for new key-value entry
               (env/track-allocation! env (unchecked-add 64 (long (env/estimate-size value)))))
             (.put data key value)))))
     value)))

;;; Metatable operations

;; Global fallback for type-level metatables set during sandbox initialisation
;; (e.g. the string metatable installed by sandbox-full/sandbox-standard).
;; Per-execution overrides live in (:type-metatables env) and always take
;; precedence, so Lua code calling debug.setmetatable never leaks across runs.
(def ^:private global-type-metatables (atom {}))

(defn- type-name-of
  "Return the Lua type name string for v if it is a basic type, else nil."
  [v]
  (cond
    (nil? v) "nil"
    (boolean? v) "boolean"
    (number? v) "number"
    (string? v) "string"
    :else nil))

(defn get-type-metatable
  "Return the type-level metatable for the Lua type of value v, or nil.
   Checks the current execution environment first (set by debug.setmetatable),
   then the global fallback (set during sandbox initialisation)."
  [v]
  (when-let [tn (type-name-of v)]
    (or (when-let [cur-env env/*current-env*]
          (get @(:type-metatables cur-env) tn))
        (get @global-type-metatables tn))))

(defn set-type-metatable!
  "Set the type-level metatable for the Lua type of value v.
   When called during Lua execution (*current-env* bound), stores in the
   per-execution environment — changes never leak to other runs.
   When called during sandbox setup (no *current-env*), stores in the global
   fallback (sandbox-level defaults like the string metatable).
   Pass mt=nil to clear."
  [v mt]
  (when-let [tn (type-name-of v)]
    (let [target (if env/*current-env*
                   (:type-metatables env/*current-env*)
                   global-type-metatables)]
      (if (nil? mt)
        (swap! target dissoc tn)
        (swap! target assoc tn mt)))))

(defn get-metatable
  "Get metatable of a table or userdata value, or nil.
   Lua tables use an object-array slot for their metatable.
   Non-table maps (e.g. file handles) carry a :clua-metatable key.
   Basic types (number, boolean, nil, string) use type-level metatables."
  [value]
  (cond
    (types/lua-table? value)
    (aget ^objects (:metatable value) 0)
    (and (map? value) (some? (:clua-metatable value)))
    (:clua-metatable value)
    :else (get-type-metatable value)))

(defn set-metatable!
  "Set metatable of a table. Returns the table."
  [table mt]
  (when (types/lua-table? table)
    (aset ^objects (:metatable table) 0 mt))
  table)

(defn get-metamethod
  "Get a metamethod from value's metatable."
  [value method-name]
  (when-let [mt (get-metatable value)]
    (table-get mt method-name)))

(defn lua-type-name
  "Return the Lua type name for error messages, checking __name in metatable.
   Unlike types/lua-type, returns the __name string from the value's metatable
   when present (e.g. 'FILE*' for file handles, 'My Type' for user-tagged tables)."
  [v]
  (cond
    (nil? v) "nil"
    (boolean? v) "boolean"
    (number? v) "number"
    (string? v) "string"
    (fn? v) "function"
    (and (map? v) (= :lua-function (:type v))) "function"
    (and (map? v) (= :lua-coroutine (:type v))) "thread"
    :else
    (let [name-val (when-let [mt (get-metatable v)]
                     (let [nv (table-get mt "__name")]
                       (when (string? nv) nv)))]
      (or name-val
          (cond
            (types/lua-table? v) "table"
            (and (map? v) (:clua-metatable v)) "userdata"
            :else "userdata")))))

(defn table-get-with-meta
  "Get a value from a table or userdata, respecting __index metamethod.
   For non-lua-table maps (e.g. file handles with :clua-metatable), skips the
   raw-value lookup and goes directly to the __index metamethod."
  [table key env]
  (let [raw-value (when (types/lua-table? table) (table-get table key))]
    (if (some? raw-value)
      raw-value
      (when-let [index-mm (get-metamethod table "__index")]
        (cond
          ;; __index is a table - recursive lookup
          (types/lua-table? index-mm)
          (table-get-with-meta index-mm key env)
          ;; __index is a function - call it
          (or (fn? index-mm) (= :lua-function (:type index-mm)))
          (let [result (call-function index-mm [table key] env)]
            (if (vector? result) (first result) result))
          :else nil)))))

(defn table-get-with-meta-resumable
  "Stack-machine-aware version of table-get-with-meta.
  Returns: {:type :normal :value v} or {:type :yield :values [...]}

  This version handles metamethod yields gracefully for use in the stack machine.
  For non-lua-table maps (e.g. file handles with :clua-metatable), skips raw-value
  lookup and goes directly to the __index metamethod."
  [table key env]
  (let [raw-value (when (types/lua-table? table) (table-get table key))]
    (if (some? raw-value)
      ;; Found value directly - return it
      {:type :normal :value raw-value}
      ;; No direct value - check for __index metamethod
      (if-let [index-mm (get-metamethod table "__index")]
        (cond
          ;; __index is a table - recursive lookup
          (types/lua-table? index-mm)
          (table-get-with-meta-resumable index-mm key env)

          ;; __index is a function - call it (might yield!)
          (or (fn? index-mm) (= :lua-function (:type index-mm)))
          (try
            ;; Call the metamethod
            (let [result (call-function index-mm [table key] env)
                  ;; Unwrap vector results (multi-value)
                  final-value (if (vector? result) (first result) result)]
              {:type :normal :value final-value})
            (catch ExceptionInfo e
              ;; Check if it's a yield
              (if (= :coro-yield (:type (ex-data e)))
                ;; Metamethod yielded - return yield result
                (let [coro-runtime-ns (find-ns 'clua.interpreter.coro-runtime)
                      get-current-coro (when coro-runtime-ns
                                         (ns-resolve coro-runtime-ns 'get-current-coroutine))
                      coro-state (when get-current-coro (get-current-coro))
                      yield-state (when coro-state
                                    (:pending-yield-state @(:state coro-state)))]
                  (when coro-state
                    (swap! (:state coro-state) dissoc :pending-yield-state))
                  {:type :yield
                   :values (if yield-state
                             (:values yield-state)
                             (:values (ex-data e)))})
                ;; Other exception - re-throw
                (throw e))))

          ;; __index is neither table nor function
          :else
          {:type :normal :value nil})
        ;; No __index metamethod
        {:type :normal :value nil}))))

(defn table-set-with-meta!
  "Set a value in a table, respecting __newindex metamethod.
   When __newindex is a table, follows the chain iteratively (like PUC-Lua)
   up to 100 hops; throws on loop detection."
  [table key value env]
  (loop [t table iters 0]
    (when-not (types/lua-table? t)
      (throw (ex-info (str "attempt to index a " (lua-type-name t) " value")
                      {:type :error})))
    (when (> iters 100)
      (throw (ex-info "'__newindex' chain too long; possible loop"
                      {:type :error})))
    (let [existing (table-get t key)]
      (if (some? existing)
        (table-set! t key value env)
        (if-let [mm (get-metamethod t "__newindex")]
          (cond
            (types/lua-table? mm)
            (recur mm (inc iters))
            (or (fn? mm) (= :lua-function (:type mm)))
            (do (try
                  (call-function mm [t key value] env)
                  (catch ExceptionInfo e
                    (throw (ex-info (str (ex-message e) "\n\t(in metamethod '__newindex')")
                                    (ex-data e)))))
                value)
            :else (table-set! t key value env))
          (table-set! t key value env))))))

;;; Metamethod mappings

(def binary-metamethods
  "Mapping of binary operators to metamethod names."
  {"+" "__add", "-" "__sub", "*" "__mul", "/" "__div",
   "//" "__idiv", "%" "__mod", "^" "__pow", ".." "__concat",
   "&" "__band", "|" "__bor", "~" "__bxor", "<<" "__shl", ">>" "__shr"})

(def unary-metamethods
  "Mapping of unary operators to metamethod names."
  {"-" "__unm", "#" "__len", "~" "__bnot"})

(defn try-binary-metamethod
  "Try to apply a binary metamethod for the given operator and operands."
  [op left right env]
  (when-let [mm-name (get binary-metamethods op)]
    (when-let [mm (or (get-metamethod left mm-name)
                      (get-metamethod right mm-name))]
      (let [result (call-function mm [left right] env)]
        (if (vector? result) (first result) result)))))

(defn table-sequence-len
  "Returns the effective sequence length of a table by finding the last non-nil
   element in the array part. Implements Lua's # operator semantics."
  [t]
  (let [^ArrayList arr (:array t)
        size (.size arr)]
    (loop [n (dec size)]
      (if (or (< n 0) (not (nil? (.get arr n))))
        (inc n)
        (recur (dec n))))))

(defn try-unary-metamethod
  "Try to apply a unary metamethod for the given operator and operand."
  [op val env]
  (when-let [mm-name (get unary-metamethods op)]
    (when-let [mm (get-metamethod val mm-name)]
      (let [result (call-function mm [val] env)]
        (if (vector? result) (first result) result)))))

(defn try-comparison-metamethod
  "Try to apply a comparison metamethod for the given operator and operands.
   Returns [success result] where success indicates if metamethod was found."
  [op left right env]
  (case op
    ;; __eq: only called if BOTH operands have the SAME __eq metamethod (same reference)
    "==" (let [left-eq (get-metamethod left "__eq")
               right-eq (get-metamethod right "__eq")]
           (if (and left-eq (identical? left-eq right-eq))
             [true (types/lua-truthy? (let [r (call-function left-eq [left right] env)]
                                        (if (vector? r) (first r) r)))]
             [false nil]))
    ;; __lt: check left first, then right
    "<" (if-let [mm (or (get-metamethod left "__lt")
                        (get-metamethod right "__lt"))]
          [true (types/lua-truthy? (let [r (call-function mm [left right] env)]
                                     (if (vector? r) (first r) r)))]
          [false nil])
    ;; __le: try __le first, then fall back to not (b < a) using __lt
    "<=" (if-let [mm (or (get-metamethod left "__le")
                         (get-metamethod right "__le"))]
           [true (types/lua-truthy? (let [r (call-function mm [left right] env)]
                                      (if (vector? r) (first r) r)))]
           ;; Fall back to not (right < left)
           (if-let [lt-mm (or (get-metamethod right "__lt")
                              (get-metamethod left "__lt"))]
             [true (not (types/lua-truthy? (let [r (call-function lt-mm [right left] env)]
                                             (if (vector? r) (first r) r))))]
             [false nil]))
    ;; > uses < with swapped operands
    ">" (try-comparison-metamethod "<" right left env)
    ;; >= uses <= with swapped operands
    ">=" (try-comparison-metamethod "<=" right left env)
    ;; ~= uses == and negates
    "~=" (let [[found result] (try-comparison-metamethod "==" left right env)]
           (if found
             [true (not result)]
             [false nil]))
    [false nil]))
