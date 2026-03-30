(ns clua.interpreter.convert
  "Bidirectional conversion between Clojure data and Lua values."
  (:require [clua.interpreter.tables :as tables]
            [clua.interpreter.types :as types])
  (:import (java.util ArrayList HashMap)))
(set! *warn-on-reflection* true)


(defn clj->lua
  "Recursively converts Clojure data to Lua-compatible values.

   - nil, booleans, numbers, strings → pass through unchanged
   - keywords → string (via name)
   - maps → lua-table with converted keys (keyword→name, string→as-is, number→as-is, other→str)
             values are converted recursively
   - vectors/seqs → lua-table with 1-based integer keys, values converted recursively
   - lua-tables, functions, lua-functions, and all other values → pass through unchanged"
  [v]
  (cond
    (or (nil? v) (boolean? v) (number? v) (string? v)) v
    (keyword? v) (name v)
    (types/lua-table? v) v
    (fn? v) v
    (and (map? v) (= :lua-function (:type v))) v
    (map? v)
    (let [t (tables/make-table)]
      (doseq [[k val] v]
        (let [lua-key (cond
                        (keyword? k) (name k)
                        (string? k) k
                        (number? k) k
                        :else (str k))]
          (tables/table-set! t lua-key (clj->lua val))))
      t)
    (sequential? v)
    (let [t (tables/make-table)]
      (doseq [[i item] (map-indexed vector v)]
        (tables/table-set! t (unchecked-inc (long i)) (clj->lua item)))
      t)
    :else v))

(defn- convert-key
  "Convert a table key: string keys use key-fn, other keys pass through."
  [k key-fn]
  (if (string? k)
    (key-fn k)
    k))

(defn lua->clj
  "Recursively converts Lua values to idiomatic Clojure data.

   - nil, booleans, numbers, strings → pass through unchanged
   - lua-table → Clojure map (1-based integer keys for array entries, string keys
     converted via key-fn for hash entries). Always a map, never a vector — this
     matches Lua's data model where all tables are associative.
   - vector (multiple return values from Lua) → each element converted
   - functions, lua-functions, and all other values → pass through unchanged

   key-fn controls how string table keys are converted:
   - keyword (default) → keywords, e.g. :name
   - identity or nil   → keep as strings, e.g. \"name\"

   To skip conversion entirely and receive raw Lua values, use :key-fn false
   in clua.core/execute — that bypasses lua->clj altogether."
  ([v] (lua->clj v keyword))
  ([v key-fn]
   (let [kfn (or key-fn identity)]
     (cond
       (types/lua-table? v)
       (let [^ArrayList arr (:array v)
             ^HashMap data (:data v)
             arr-size (.size arr)
             dat-size (.size data)]
         (if (and (zero? arr-size) (zero? dat-size))
           {}
           (merge
             (when (pos? arr-size)
               (into {} (map-indexed (fn [i item]
                                       [(unchecked-inc (long i)) (lua->clj item kfn)])
                                     arr)))
             (when (pos? dat-size)
               (into {} (map (fn [[k val]]
                               [(convert-key k kfn) (lua->clj val kfn)])
                             data))))))

       (vector? v)
       ;; Multiple return values — convert each element
       (mapv #(lua->clj % kfn) v)

       :else v))))
