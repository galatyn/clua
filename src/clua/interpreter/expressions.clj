(ns clua.interpreter.expressions
  "Expression evaluation multimethod and implementations for the Lua interpreter."
  (:require [clua.interpreter.coro-runtime :as coro]
            [clua.interpreter.env :as env]
            [clua.interpreter.operators :as ops]
            [clua.interpreter.tables :as tables]
            [clua.interpreter.types :as types])
  (:import (java.util HashMap)))
(set! *warn-on-reflection* true)


;; Forward declarations for functions defined in other modules
(declare call-function)
(declare operand-context-desc)

;;; Helper functions (exposed for use by other interpreter modules)

(defn update-position!
  "Update the current execution position from a node.
   Uses line/column if available, otherwise uses stmt-index.
   Checks both direct node keys and metadata."
  [node env]
  (when (or (map? node) (vector? node))
    (let [;; Try to get position from metadata first, then from direct keys
          node-meta (meta node)
          line (or (:line node) (:line node-meta))
          column (or (:column node) (:column node-meta))
          stmt-idx (:stmt-index node)]
      (cond
        ;; Prefer line/column if available
        line
        (env/set-position! env line column stmt-idx)
        ;; Fall back to statement index (1-indexed for display)
        stmt-idx
        (env/set-position! env nil nil (unchecked-inc (long stmt-idx)))))))

;;; Expression evaluation multimethod

(defmulti eval-exp
  "Evaluate an expression node."
  (fn [node _env] (:type node)))

(defmethod eval-exp :nil [_node _env]
  nil)

(defmethod eval-exp :boolean [node _env]
  (:value node))

(defmethod eval-exp :number [node _env]
  (:value node))

(defmethod eval-exp :string [node _env]
  (:value node))

(defmethod eval-exp :name [node env]
  (env/lookup env (:value node)))

(defn expand-vararg-table
  "Expand '...' from a named vararg table (Lua 5.5 ...t syntax).
   Validates t.n: must be a non-negative integer <= Integer/MAX_VALUE.
   Throws 'no proper n' error for invalid n values."
  [vt]
  (let [raw (tables/table-get vt "n")]
    (if (nil? raw)
      []
      (do
        (when (or (not (integer? raw))
                  (neg? (long raw))
                  (> (long raw) Integer/MAX_VALUE))
          (throw (ex-info "no proper 'n' field in vararg table" {:type :error})))
        (mapv #(tables/table-get vt %) (range 1 (inc (long raw))))))))

(defmethod eval-exp :vararg [_node env]
  ;; Return varargs stored in the environment.
  ;; For Lua 5.5 named vararg (...t), "..." is {:vararg-table t} — expand live from the table.
  (let [v (env/lookup env "...")]
    (cond
      ;; Named vararg: expand t[1]..t[t.n] from the live table
      (and (map? v) (:vararg-table v))
      (expand-vararg-table (:vararg-table v))
      ;; Regular vararg: plain vector
      (vector? v) v
      :else [])))

(defmethod eval-exp :binary-exp [node env]
  (env/increment-steps! env)
  (update-position! node env)
  (let [op (:op node)
        ;; Short-circuit evaluation for and/or
        left-val (types/unwrap-single (eval-exp (:left node) env))]
    (case op
      "and" (if (types/lua-truthy? left-val)
              (types/unwrap-single (eval-exp (:right node) env))
              left-val)
      "or" (if (types/lua-truthy? left-val)
             left-val
             (types/unwrap-single (eval-exp (:right node) env)))
      ;; Non-short-circuit operators
      (let [right-val (types/unwrap-single (eval-exp (:right node) env))
            ;; After both operands are evaluated, update position to the operator's line.
            ;; This makes errors like "nil + {}" report the + operator's line, not the
            ;; statement's line.  Only arithmetic/bitwise ops benefit; others use metamethods.
            _ (when-let [op-line (:op-line node)]
                (env/set-position! env op-line nil nil))]
        (try
          (ops/apply-binary-op op left-val right-val env)
          (catch clojure.lang.ExceptionInfo e
            (let [data (ex-data e)]
              (if (= :error (:type data))
                (let [ctx (case op
                            ("+" "-" "*" "/" "//" "%" "^")
                            (cond
                              (nil? (ops/coerce-arith left-val)) (operand-context-desc (:left node) env)
                              (nil? (ops/coerce-arith right-val)) (operand-context-desc (:right node) env))
                            ("&" "|" "~" "<<" ">>")
                            (cond
                              (nil? (ops/coerce-bitwise left-val)) (operand-context-desc (:left node) env)
                              (nil? (ops/coerce-bitwise right-val)) (operand-context-desc (:right node) env))
                            nil)]
                  (throw (ex-info (str (ex-message e) (or ctx "")) data)))
                (throw e)))))))))

(defmethod eval-exp :unary-exp [node env]
  (env/increment-steps! env)
  (update-position! node env)
  (let [val (types/unwrap-single (eval-exp (:operand node) env))
        op (:op node)
        ;; Re-update position to the operator's line after operand evaluation.
        ;; The operand may have moved the position cursor; reset it to the operator
        ;; so that errors thrown below report the correct line.
        _ (when-let [op-line (:op-line node)]
            (env/set-position! env op-line nil nil))]
    (case op
      "-" (if (number? val)
            (if (integer? val)
              (unchecked-negate (long val))
              (- (double val)))
            (let [coerced (ops/coerce-arith val)]
              (if (number? coerced)
                (if (integer? coerced)
                  (unchecked-negate (long coerced))
                  (- (double coerced)))
                (or (tables/try-unary-metamethod op val env)
                    (throw (ex-info (str "attempt to perform arithmetic on a "
                                         (tables/lua-type-name val) " value"
                                         (or (operand-context-desc (:operand node) env) ""))
                                    {:type :error}))))))
      "not" (not (types/lua-truthy? val))
      "#" (cond
            (string? val) (count val)
            (types/lua-table? val)
            (if-let [len-result (tables/try-unary-metamethod op val env)]
              len-result
              (tables/table-sequence-len val))
            :else (throw (ex-info (str "attempt to get length of a "
                                       (tables/lua-type-name val) " value")
                                  {:type :error})))
      "~" (let [coerced (ops/coerce-bitwise val)]
            (if (some? coerced)
              (bit-not (long coerced))
              (or (tables/try-unary-metamethod op val env)
                  (throw (ex-info (str (ops/bitwise-error-msg val)
                                       (or (operand-context-desc (:operand node) env) ""))
                                  {:type :error}))))))))

(defmethod eval-exp :table [node env]
  (let [table (tables/make-table env)
        array-idx (atom 1)
        ;; Handle nested fields structure from parser - flatten and filter out :fieldsep
        raw-fields (:fields node)
        fields (if (and (seq raw-fields)
                        (vector? (first raw-fields))
                        (not (keyword? (first (first raw-fields)))))
                 ;; Fields are nested: [[{...} [:fieldsep] {...}]] -> flatten and filter
                 (->> (first raw-fields)
                      (filter #(and (map? %) (:type %))))
                 ;; Fields are flat: [{...} {...}]
                 raw-fields)
        num-fields (count fields)]
    (doseq [[idx field] (map-indexed vector fields)]
      (let [is-last (= idx (dec num-fields))]
        (cond
          (= :array-field (:type field))
          (let [value-node (:value field)
                val (eval-exp value-node env)]
            ;; If last array field is a multi-value expr (vararg/function call), spread it
            (if (and is-last (types/is-multi-value-expr? value-node) (vector? val))
              (doseq [v val]
                (tables/table-set! table @array-idx v env)
                (swap! array-idx inc))
              (do
                (tables/table-set! table @array-idx val env)
                (swap! array-idx inc))))

          (= :bracket-field (:type field))
          (let [key (eval-exp (:key field) env)             ; Always evaluate key expression
                val (eval-exp (:value field) env)]
            (tables/table-set! table key val env))

          (= :name-field (:type field))
          (let [key (:value (:name field))                  ; Use name string as key
                val (eval-exp (:value field) env)]
            (tables/table-set! table key val env))

          (= :field (:type field))
          (let [key (if (= :name (:type (:key field)))
                      (:value (:key field))
                      (eval-exp (:key field) env))
                val (eval-exp (:value field) env)]
            (tables/table-set! table key val env)))))
    table))

(defn value-source-desc
  "Return ' (global 'name')', ' (local 'name')', or ' (upvalue 'name')' for error messages, or nil.
   Variables in scopes captured by the current closure are 'upvalue'; those defined in the
   current function body (scopes from :outer-scope-count onward) are 'local'."
  [obj-node env]
  (when (and (map? obj-node) (= :name (:type obj-node)))
    (let [name (:value obj-node)
          scopes (:scopes env)
          outer-count (or (:outer-scope-count env) 0)
          found-idx (first (keep-indexed (fn [i scope]
                                           (when (and (instance? HashMap scope)
                                                      (.containsKey ^HashMap scope name))
                                             i))
                                         scopes))
          label (cond
                  (nil? found-idx) "global"
                  (< (long found-idx) (long outer-count)) "upvalue"
                  :else "local")]
      (str " (" label " '" name "')"))))

(defn operand-context-desc
  "Return context suffix for an operand node: handles :name and :field-access.
   Returns ' (global/local 'name')' for :name, ' (field 'name')' for :field-access, nil otherwise."
  [node env]
  (when (map? node)
    (case (:type node)
      :name (value-source-desc node env)
      :field-access
      (let [field (:field node)
            fname (when (and (map? field) (= :name (:type field))) (:value field))]
        (when fname (str " (field '" fname "')")))
      nil)))

(defmethod eval-exp :index-access [node env]
  (env/increment-steps! env)
  (update-position! node env)
  (let [obj (eval-exp (:object node) env)
        idx (types/unwrap-single (eval-exp (:index node) env))]
    (cond
      (nil? obj)
      (throw (ex-info (str "attempt to index a nil value"
                           (value-source-desc (:object node) env))
                      {:type :error}))
      (types/lua-table? obj) (tables/table-get-with-meta obj idx env)
      ;; Non-table userdata with metatable (e.g. file handles)
      (and (map? obj) (:clua-metatable obj)) (tables/table-get-with-meta obj idx env)
      ;; String indexing - character at integer position
      (string? obj) (when (and (number? idx) (let [li (long idx)] (and (pos? li) (<= li (count obj)))))
                      (str (nth obj (dec (int idx)))))
      ;; Basic types (number, boolean) with type-level __index metamethod
      (tables/get-type-metatable obj) (tables/table-get-with-meta obj idx env)
      ;; Other types - error
      :else
      (throw (ex-info (str "attempt to index a " (tables/lua-type-name obj) " value"
                           (value-source-desc (:object node) env))
                      {:type :error})))))

(defmethod eval-exp :field-access [node env]
  (env/increment-steps! env)
  (update-position! node env)
  (let [obj (eval-exp (:object node) env)
        field-name (:value (:field node))]
    (cond
      (nil? obj)
      (throw (ex-info (str "attempt to index a nil value"
                           (value-source-desc (:object node) env))
                      {:type :error}))
      (types/lua-table? obj) (tables/table-get-with-meta obj field-name env)
      ;; Non-table userdata with metatable (e.g. file handles)
      (and (map? obj) (:clua-metatable obj)) (tables/table-get-with-meta obj field-name env)
      ;; String field access - look up in string library (e.g. s.sub -> string.sub)
      (string? obj) (when-let [string-lib (env/lookup env "string")]
                      (tables/table-get string-lib field-name))
      ;; Basic types (number, boolean) with type-level __index metamethod
      (tables/get-type-metatable obj) (tables/table-get-with-meta obj field-name env)
      ;; Other types - error
      :else
      (throw (ex-info (str "attempt to index a " (tables/lua-type-name obj) " value"
                           (value-source-desc (:object node) env))
                      {:type :error})))))

(defmethod eval-exp :function-def [node env]
  ;; Capture the environment for closures
  (let [func-body (:body node)
        param-list (:params func-body)
        ;; Extract parameter names and check for varargs
        ;; {:type :param-list, :params [{:type :name-list, :names [...]} {:type :vararg}]}
        ;; or {:type :param-list, :params [{:type :vararg}]}
        [param-names has-varargs vararg-name]
        (if param-list
          (let [params (:params param-list)
                vararg-node (some #(when (= :vararg (:type %)) %) params)
                has-vararg (boolean vararg-node)
                name-params (filter #(not= :vararg (:type %)) params)
                names (cond
                        ;; namelist inside params
                        (and (= 1 (count name-params))
                             (= :name-list (:type (first name-params))))
                        (mapv #(:value %) (:names (first name-params)))
                        ;; Direct name nodes
                        (seq name-params)
                        (mapv #(:value %) name-params)
                        :else
                        [])]
            [names has-vararg (:name vararg-node)])
          [[] false nil])
        lua-func {:type :lua-function
                  :params param-names
                  :varargs has-varargs
                  :vararg-name vararg-name
                  :body (:body func-body)
                  :env env
                  :line-defined (or (:line func-body) -1)
                  :last-line-defined (or (:last-line func-body) -1)}]
    ;; Mark as yieldable if it contains yields (on-demand during execution)
    ;; This is already optimal - only checks/marks functions with yields
    (coro/mark-yieldable lua-func)))

(defn eval-single-value
  "Evaluate an expression, but if it returns multiple values (function call or vararg),
   only take the first value (Lua semantics for non-last position)."
  [node env]
  (let [val (eval-exp node env)]
    (if (and (types/is-multi-value-expr? node) (vector? val))
      (first val)
      val)))

(defn extract-args
  "Extract argument values from an args node.
   In Lua, if the last argument is a multi-value expression (function call or vararg),
   its multiple values are spread as additional arguments. Multi-value expressions
   in non-last positions only contribute their first value."
  [args-node env]
  (if-let [values (:values args-node)]
    (let [arg-nodes (if (and (= 1 (count values))
                             (= :exp-list (:type (first values))))
                      (:values (first values))
                      values)]
      (if (empty? arg-nodes)
        []
        ;; Evaluate all but the last argument - only first value for multi-value exprs
        (let [init-args (mapv #(eval-single-value % env) (butlast arg-nodes))
              last-node (last arg-nodes)
              last-val (eval-exp last-node env)]
          ;; If the last argument is a multi-value expression, spread into arg list
          (if (and (types/is-multi-value-expr? last-node)
                   (vector? last-val))
            (into init-args last-val)
            (conj init-args last-val)))))
    []))

(defn convert-packed-args
  "Convert a packed-args marker (from table.pack) to a proper Lua table."
  [packed env]
  (let [table (tables/make-table env)]
    ;; Set array elements (1-indexed)
    (doseq [[i v] (map-indexed vector (:values packed))]
      (tables/table-set! table (unchecked-inc (long i)) v env))
    ;; Set the 'n' field with the count
    (tables/table-set! table "n" (:n packed) env)
    table))

(defn maybe-convert-result
  "Convert special return values (like packed-args) to proper Lua types."
  [result env]
  (if (and (map? result) (= :packed-args (:type result)))
    (convert-packed-args result env)
    result))

(defn get-call-name
  "Extract a human-readable name for a function call target."
  [target-node]
  (cond
    (= :name (:type target-node))
    (:value target-node)

    (= :field-access (:type target-node))
    (let [field (:field target-node)]
      (if (and (map? field) (= :name (:type field)))
        (:value field)
        field))

    (= :index-access (:type target-node))
    (str (get-call-name (:object target-node)) "[...]")

    :else nil))

(defn get-call-namewhat
  "Determine namewhat for a function call target.
   Returns 'local', 'global', 'field', or ''."
  [target-node env]
  (case (:type target-node)
    :name
    (let [var-name (:value target-node)
          result (if (some (fn [^HashMap scope] (.containsKey scope var-name))
                           (rseq (:scopes env)))
                   "local"
                   "global")]
      result)
    (:field-access :index-access) "field"
    ""))

(defmethod eval-exp :function-call [node env]
  (env/increment-steps! env)
  (update-position! node env)
  (let [target (eval-single-value (:target node) env)
        arg-values (extract-args (:args node) env)
        fn-name (get-call-name (:target node))
        fn-namewhat (get-call-namewhat (:target node) env)
        line (:line node)
        col (:column node)]
    ;; Push stack frame before calling
    (env/push-stack-frame! env fn-name line col target nil 0 fn-namewhat)
    (try
      (call-function target arg-values env)
      (catch clojure.lang.ExceptionInfo e
        (let [data (ex-data e)]
          (if (= :call-error (:type data))
            (let [ctx (operand-context-desc (:target node) env)]
              (throw (ex-info (str (ex-message e) (or ctx "")) data)))
            (throw e))))
      (finally
        ;; Always pop the stack frame
        (env/pop-stack-frame! env)))))

(defmethod eval-exp :method-call [node env]
  (env/increment-steps! env)
  (update-position! node env)
  (let [obj (eval-exp (:object node) env)
        method-name (:value (:method node))
        ;; Guard: non-indexable objects fail with an index error before method lookup
        _ (when (or (nil? obj)
                    (and (not (types/lua-table? obj))
                         (not (string? obj))
                         (not (and (map? obj) (:clua-metatable obj)))))
            (throw (ex-info (str "attempt to index a " (tables/lua-type-name obj) " value"
                                 (or (operand-context-desc (:object node) env) ""))
                            {:type :error})))
        ;; Use metatable-aware lookup for method resolution
        method (cond
                 (types/lua-table? obj)
                 (tables/table-get-with-meta obj method-name env)
                 ;; Non-table userdata with metatable (e.g. file handles)
                 (and (map? obj) (:clua-metatable obj))
                 (tables/table-get-with-meta obj method-name env)
                 ;; String method calls
                 :else
                 (when-let [string-lib (env/lookup env "string")]
                   (tables/table-get string-lib method-name)))
        arg-values (extract-args (:args node) env)
        ;; Build method call name (object:method)
        fn-name (str (get-call-name (:object node)) ":" method-name)
        line (:line node)
        col (:column node)]
    ;; Push stack frame before calling
    (env/push-stack-frame! env fn-name line col method nil)
    (try
      ;; Method call passes object as first argument (self)
      (call-function method (cons obj arg-values) env)
      (catch clojure.lang.ExceptionInfo e
        (let [data (ex-data e)]
          (if (= :call-error (:type data))
            (throw (ex-info (str (ex-message e) " (method '" method-name "')") data))
            (throw e))))
      (finally
        (env/pop-stack-frame! env)))))

(defmethod eval-exp :exp-list [node env]
  ;; In Lua, if the last expression is a multi-value expression (function call or vararg),
  ;; its values are spread. Multi-value exprs not in last position use only first value.
  (let [values (:values node)]
    (if (empty? values)
      []
      (let [init-vals (mapv #(eval-single-value % env) (butlast values))
            last-node (last values)
            last-val (eval-exp last-node env)]
        (if (and (types/is-multi-value-expr? last-node) (vector? last-val))
          (into init-vals last-val)
          (conj init-vals last-val))))))

(defmethod eval-exp :paren-exp [node env]
  ;; Parenthesized expression: (expr)
  ;; In Lua, (expr) truncates multiple values to exactly one.
  (eval-single-value (:expr node) env))

(defmethod eval-exp :default [node _env]
  ;; Handle any unexpected node types
  (cond
    (nil? node) nil
    (not (map? node)) node
    (:value node) (:value node)
    :else nil))
