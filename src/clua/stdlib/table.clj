(ns clua.stdlib.table
  "Lua table library implementation.

   Implements Lua 5.3 table manipulation functions.
   Tables in CLua have two parts:
   - :array - vector for sequential integer keys (1-based)
   - :data  - map for non-sequential/non-integer keys"
  (:require [clojure.string :as str]
            [clua.interpreter.env :as env]
            [clua.interpreter.tables :as tables]
            [clua.interpreter.types :refer [lua-table?]]))
(set! *warn-on-reflection* true)


;; =============================================================================
;; Helper Functions
;; =============================================================================

(defn- track-memory!
  "Track memory allocation if environment is available.
   size-estimate is the number of bytes to track."
  [size-estimate]
  (when-let [current-env env/*current-env*]
    (env/track-allocation! current-env size-estimate)))

;; =============================================================================
;; Table Library Functions
;; =============================================================================

(defn- table-integer-len
  "Get the integer length of a table, checking __len metamethod.
   Throws 'object length is not an integer' if __len returns a non-integer."
  [t]
  (if-let [len-mm (tables/get-metamethod t "__len")]
    (let [result (tables/call-function len-mm [t] env/*current-env*)
          result (if (vector? result) (first result) result)]
      (if (and (number? result) (integer? result))
        (long result)
        (throw (ex-info "object length is not an integer" {:type :error}))))
    (tables/table-sequence-len t)))

(defn- tget
  "Get element at integer key k via metamethods."
  [t k]
  (tables/table-get-with-meta t k env/*current-env*))

(defn- tset!
  "Set element at integer key k via metamethods."
  [t k v]
  (tables/table-set-with-meta! t k v env/*current-env*))

(defn lua-insert
  "table.insert(list, [pos,] value)
   Inserts value at position pos in list, shifting elements up.
   If pos is omitted, appends value at the end."
  [t & args]
  (track-memory! 24)
  (case (count args)
    1                                                       ;; table.insert(t, value) - append
    (let [len (long (table-integer-len t))]
      (tset! t (unchecked-inc len) (first args))
      nil)
    2                                                       ;; table.insert(t, pos, value) - insert at position
    (let [[pos val] args
          pos (long pos)
          len (long (table-integer-len t))]
      (when-not (and (>= pos 1) (<= pos (unchecked-inc len)))
        (throw (ex-info "bad argument #2 to 'insert' (position out of bounds)"
                        {:type :error})))
      ;; Shift elements up from len down to pos
      (loop [i len]
        (when (>= i pos)
          (tset! t (unchecked-inc i) (tget t i))
          (recur (unchecked-dec i))))
      (tset! t pos val)
      nil)
    ;; Wrong number of args
    (throw (ex-info "wrong number of arguments to 'insert'" {:type :error}))))

(defn lua-remove
  "table.remove(list [, pos])
   Removes element at position pos from list, shifting elements down.
   Returns the removed element. Default pos is #list (last element).
   Valid positions: 1..len, len+1 (returns nil), or 0 when len==0."
  [t & [pos]]
  (let [len (long (table-integer-len t))
        pos (long (or pos len))]
    (cond
      ;; In-range position 1..len: get value, shift elements down, erase last
      (and (>= pos 1) (<= pos len))
      (let [val (tget t pos)]
        (loop [i pos]
          (when (< i len)
            (tset! t i (tget t (unchecked-inc i)))
            (recur (unchecked-inc i))))
        (tset! t len nil)
        val)
      ;; pos = len+1: erase list[len+1] (allowed per Lua 5.3 spec)
      (= pos (unchecked-inc len))
      (let [val (tget t pos)]
        (when (some? val)
          (tset! t pos nil))
        val)
      ;; pos = 0 when len = 0: erase list[0] (allowed per Lua 5.3 spec)
      (and (= pos 0) (= len 0))
      (let [val (tget t 0)]
        (when (some? val)
          (tset! t 0 nil))
        val)
      ;; All other positions: out of bounds
      :else
      (throw (ex-info "bad argument #2 to 'remove' (position out of bounds)"
                      {:type :error})))))

(defn lua-concat
  "table.concat(list [, sep [, i [, j]]])
   Returns list[i]..sep..list[i+1]...sep..list[j].
   Default sep is empty string, i is 1, j is #list."
  [t & [sep i j]]
  (when-not (lua-table? t)
    (throw (ex-info "bad argument #1 to 'concat' (table expected)" {:type :error})))
  (let [sep (or sep "")
        i (long (or i 1))
        j (long (or j (table-integer-len t)))]
    (cond
      ;; Check i > j first before any arithmetic that could overflow
      (> i j) ""
      ;; If range is too large (> 100M elements), it's not practical.
      ;; Use Math/subtractExact to avoid overflow when i is Long.MIN_VALUE
      (let [range-size (long (try (Math/subtractExact j i)
                                  (catch ArithmeticException _ Long/MAX_VALUE)))]
        (> range-size 100000000))
      (throw (ex-info "range too large" {:type :error}))
      ;; Normal case: iterate through range via metamethods
      :else
      (let [values (loop [idx i
                          result []]
                     (if (<= idx j)
                       (let [val (tget t idx)]
                         ;; Validate value type (must be string or number; nil is invalid)
                         (when-not (or (string? val) (number? val))
                           (let [type-name (if (nil? val) "nil" (tables/lua-type-name val))]
                             (throw (ex-info (str "invalid value (" type-name ") at index " idx " in table for 'concat'")
                                             {:type :error}))))
                         (if (>= idx j)
                           (conj result val)
                           (recur (unchecked-inc idx) (conj result val))))
                       result))]
        (str/join sep values)))))

(defn lua-sort
  "table.sort(list [, comp])
   Sorts list elements in place. If comp is given, it must be a function
   that receives two elements and returns true when first < second."
  [t & [comp-fn]]
  (when-not (lua-table? t)
    (throw (ex-info (str "bad argument #1 to 'table.sort' (table expected, got "
                         (tables/lua-type-name t) ")")
                    {:type :error})))
  (let [raw-len (table-integer-len t)]
    (when (and (number? raw-len) (> (long raw-len) Integer/MAX_VALUE))
      (throw (ex-info "too big" {:type :error})))
    (let [len (if (and (number? raw-len) (> (long raw-len) 0))
                (long raw-len)
                0)]
      (when (> len 1)
        ;; Collect elements via metamethods (supports __index proxies)
        (let [sort-list (java.util.ArrayList.)
              _ (dotimes [i len]
                  (.add sort-list (tget t (inc i))))
              lua-lt (fn [a b]
                       (cond
                         (and (number? a) (number? b)) (< (double a) (double b))
                         (and (string? a) (string? b)) (neg? (.compareTo ^String a ^String b))
                         :else
                         (let [[found result]
                               (tables/try-comparison-metamethod "<" a b env/*current-env*)]
                           (if found
                             result
                             (throw (ex-info
                                      (str "attempt to compare two " (tables/lua-type-name a) " values")
                                      {:type :error}))))))]
          (java.util.Collections/sort sort-list
                                      (reify java.util.Comparator
                                        (compare [_ a b]
                                          (if comp-fn
                                            (let [call! (fn [f x y]
                                                          (try
                                                            (let [r (tables/call-function f [x y] env/*current-env*)]
                                                              (if (vector? r) (first r) r))
                                                            (catch clojure.lang.ExceptionInfo e
                                                              (if (= :coro-yield (:type (ex-data e)))
                                                                (throw (ex-info "attempt to yield across a C-call boundary"
                                                                                {:type :error}))
                                                                (throw e)))))
                                                  fwd (call! comp-fn a b)]
                                              (when fwd
                                                (when (call! comp-fn b a)
                                                  (throw (ex-info "invalid order function for sorting" {:type :error}))))
                                              (if fwd -1 1))
                                            (cond
                                              (lua-lt a b) -1
                                              (lua-lt b a) 1
                                              :else 0)))))
          ;; Write sorted elements back via metamethods (supports __newindex proxies)
          (dotimes [i len]
            (tset! t (inc i) (.get sort-list i)))))))
  nil)

(defn- move-copy-element
  "Copy one element from position i in src to position (t + i - f) in dest.
   Respects __index/__newindex metamethods (Lua 5.3 table.move semantics).
   Uses unchecked arithmetic to handle extreme integer values (Long.MIN/MAX_VALUE)."
  [src dest f t i]
  (let [lf (long f) lt (long t) li (long i)
        src-val (tables/table-get-with-meta src li env/*current-env*)
        dest-pos (unchecked-add lt (unchecked-subtract li lf))]
    (tables/table-set-with-meta! dest dest-pos src-val env/*current-env*)))

(defn lua-move
  "table.move(a1, f, e, t [, a2])
   Moves elements from table a1 to table a2 (or a1 if a2 not given).
   Copies elements a1[f], a1[f+1], ..., a1[e] to a2[t], a2[t+1], ...
   Respects __index and __newindex metamethods.
   Returns the destination table."
  [a1 f e t & [a2]]
  (when-not (lua-table? a1)
    (throw (ex-info "bad argument #1 to 'move' (table expected)" {:type :error})))
  (let [a2 (or a2 a1)
        f (long f)
        e (long e)
        t (long t)]
    (when (<= f e)
      ;; count = e - f + 1. Use unchecked; if ≤ 0, it overflowed → too many elements.
      (let [count (unchecked-add (unchecked-subtract e f) 1)]
        (when (<= count 0)
          (throw (ex-info "too many elements to move" {:type :error})))
        ;; diff = count - 1 = e - f (valid non-negative since count > 0)
        (let [diff (unchecked-subtract e f)]
          ;; wrap-around check: t + diff > Long.MAX_VALUE ↔ t > Long.MAX_VALUE - diff
          (when (> t (- Long/MAX_VALUE diff))
            (throw (ex-info "destination wrap around" {:type :error})))
          ;; Backward copy when same table and t >= f (using unchecked subtraction to match
          ;; Lua's signed-overflow semantics: t - f with overflow → still ≥ 0 means backward).
          (if (and (identical? a1 a2) (>= (unchecked-subtract t f) 0))
            (dotimes [k count]
              (move-copy-element a1 a2 f t (unchecked-subtract e k)))
            (dotimes [k count]
              (move-copy-element a1 a2 f t (unchecked-add f k)))))))
    a2))

(defn lua-pack
  "table.pack(...)
   Returns a new table with all arguments stored into keys 1, 2, etc.
   and with a field 'n' with the total number of arguments."
  [& args]
  ;; This function needs access to the table constructor, so we return
  ;; a special marker that will be handled by the interpreter
  {:type :packed-args
   :values (vec args)
   :n (count args)})

(defn lua-unpack
  "table.unpack(list [, i [, j]])
   Returns list[i], list[i+1], ..., list[j].
   Default i is 1, j is #list.
   Throws 'too many results' if the range exceeds 1,000,000 elements."
  [t & [i j]]
  (let [i (long (or i 1))
        j (long (or j (table-integer-len t)))]
    (when (<= i j)
      ;; Overflow-safe count check: throw if range > 1,000,000 elements
      (let [cnt (try (Math/subtractExact j i)
                     (catch ArithmeticException _ Long/MAX_VALUE))]
        (when (> (long cnt) 1000000)
          (throw (ex-info "too many results" {:type :error})))))
    (if (> i j)
      []
      ;; Iterate element-by-element via metamethods (handles __index proxies)
      (let [result (java.util.ArrayList.)]
        (loop [k i]
          (.add result (tget t k))
          (when (< k j)
            (recur (inc k))))
        (vec result)))))

;; =============================================================================
;; Export as Lua library table
;; =============================================================================

;; Lua 5.5: max hash size = 2^MAXHBITS where MAXHBITS = 26.
;; Values that fit in a non-negative C int (0..2^31-1) but exceed this are
;; "table overflow"; values >= 2^31 (don't fit in C int) are "out of range".
(def ^:const ^:private max-hsize (bit-shift-left 1 26))     ; 67108864

(defn lua-create
  "table.create(n [, h]) — create table with pre-allocated capacity.
   Validates array/hash sizes per Lua 5.5 limits; actual pre-allocation is a
   no-op on the JVM (cannot replicate C struct-sized memory allocation)."
  ([] (tables/make-table))
  ([n] (lua-create n 0))
  ([n h]
   (let [n (long n)
         h (long h)]
     (when (or (neg? n) (> n Integer/MAX_VALUE))
       (throw (ex-info "bad argument #1 to 'create' (out of range)" {:type :error})))
     (when (or (neg? h) (> h Integer/MAX_VALUE))
       (throw (ex-info "bad argument #2 to 'create' (out of range)" {:type :error})))
     (when (> h max-hsize)
       (throw (ex-info "table overflow" {:type :error})))
     (tables/make-table))))

(def table-lib
  "The complete table library for Lua."
  {"insert" lua-insert
   "remove" lua-remove
   "concat" lua-concat
   "sort" lua-sort
   "move" lua-move
   "pack" lua-pack
   "unpack" lua-unpack
   "create" lua-create})
