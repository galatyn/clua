(ns clua.interpreter.types
  "Type checking and value utilities for the Lua interpreter."
  (:import (java.io Writer)
           (java.util ArrayList HashMap)))

(set! *warn-on-reflection* true)

;;; Basic type predicates

(defn lua-nil?
  "Check if value is nil."
  [v]
  (nil? v))

(defn lua-false?
  "Check if value is false."
  [v]
  (false? v))

(defn lua-truthy?
  "Check if value is truthy in Lua (not nil and not false).
  An empty vector [] represents zero return values from a function call;
  in a single-value (boolean) context the first value is nil, so it is falsy."
  [v]
  (not (or (lua-nil? v) (lua-false? v) (and (vector? v) (empty? v)))))

(defn lua-table?-basic
  "Check if value is a Lua table (basic check, used before full lua-table? is defined)."
  [v]
  (and (map? v) (= :lua-table (:type v))))

(defn lua-table?
  "Check if value is a Lua table."
  [v]
  (and (map? v) (= :lua-table (:type v))))

(defn lua-type
  "Get the Lua type name for a value."
  [v]
  (cond
    (nil? v) "nil"
    (boolean? v) "boolean"
    (number? v) "number"
    (string? v) "string"
    (fn? v) "function"
    (lua-table?-basic v) "table"
    (and (map? v) (= :lua-function (:type v))) "function"
    (and (map? v) (= :lua-coroutine (:type v))) "thread"
    :else "userdata"))

;;; Expression helpers

(defn unwrap-single
  "If value is a vector (multiple return values), take the first. Otherwise return as-is."
  [val]
  (if (vector? val) (first val) val))

(defn is-multi-value-expr?
  "Check if an AST node can return multiple values (function call or vararg)."
  [node]
  (and (map? node)
       (#{:function-call :method-call :vararg} (:type node))))

;;; Custom printer for Lua tables to handle circular references

(defmethod print-method :lua-table [table ^Writer w]
  "Custom printer for Lua tables that handles circular references.
   Prints in format: table: 0x<hashcode> with limited contents."
  (.write w (str "table: " (Integer/toHexString (System/identityHashCode table))))

  ;; Optionally show a few entries (if not circular)
  (when (and *print-level* (pos? (long *print-level*)))
    (let [^HashMap data (:data table)
          ^ArrayList array (:array table)]
      ;; Show array size and hash size
      (.write w (str " [array-size: " (.size array)
                     ", hash-size: " (.size data) "]")))))
