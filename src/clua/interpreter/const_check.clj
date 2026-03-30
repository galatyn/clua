(ns clua.interpreter.const-check
  "Static analysis pass: enforce <const> and <close> variable attributes,
   and named vararg parameter immutability (...t syntax).

   Runs after parse-and-transform, before execution.  Errors thrown here
   are caught by load()'s existing catch block and returned as
   [nil 'chunkname:line: const variable NAME'].

   Scope model:
     - A 'scope stack' is a vector of {name -> :const | :regular} maps.
     - Lookup scans innermost (last) to outermost (first).
     - A :regular entry in an inner scope shadows a :const in an outer scope.
     - Named vararg parameters (...t) are treated as :const.
     - <close> attribute is also read-only (same enforcement as <const>).
     - Const info crosses closure boundaries: outer const names remain
       visible inside nested functions as (potentially const) upvalues.")

(declare check-block check-stmt check-exp)

;; ============================================================================
;; Scope helpers
;; ============================================================================

(defn- push-scope [scopes]
  (conj scopes {}))

(defn- declare-local [scopes name const?]
  (let [top (peek scopes)]
    (conj (pop scopes) (assoc top name (if const? :const :regular)))))

(defn- declare-global [scopes name const?]
  (let [top (peek scopes)]
    (conj (pop scopes) (assoc top name (if const? :global-const :global-regular)))))

(defn- set-strict-globals [scopes]
  (let [top (peek scopes)]
    (conj (pop scopes) (assoc top ::strict-globals? true))))

(defn- set-wildcard
  "Set the global wildcard mode (:allow or :const) in the current scope."
  [scopes mode]
  (let [top (peek scopes)]
    (conj (pop scopes) (assoc top ::wildcard mode))))

(defn- active-wildcard
  "Return the innermost active wildcard mode (:allow, :const, or nil)."
  [scopes]
  (loop [ss (rseq scopes)]
    (if (seq ss)
      (if-let [mode (get (first ss) ::wildcard)]
        mode
        (recur (rest ss)))
      nil)))

(defn- lookup-var [scopes name]
  (loop [ss (rseq scopes)]
    (if (seq ss)
      (let [entry (get (first ss) name :not-found)]
        (if (= entry :not-found)
          (recur (rest ss))
          entry))
      :not-found)))

(defn- strict-globals? [scopes]
  (loop [ss (rseq scopes)]
    (if (seq ss)
      (if (contains? (first ss) ::strict-globals?)
        true
        (recur (rest ss)))
      false)))

;; ============================================================================
;; Assignment check
;; ============================================================================

(defn- check-assign-target [scopes var-node stmt-line]
  ;; Only simple name targets can be const-violated or undeclared-global violated.
  ;; Table field/index assignments (t.x = ..., t[k] = ...) are mutations of t,
  ;; not reassignment of the variable t itself.
  (when (= :name (:type var-node))
    (let [n (:value var-node)
          status (lookup-var scopes n)]
      (cond
        (#{:const :global-const} status)
        (throw (ex-info (str "attempt to assign to const variable '" n "'")
                        {:type :error :line (or (:line var-node) stmt-line)}))
        (= status :not-found)
        (let [wc (active-wildcard scopes)]
          (cond
            (= wc :const)
            (throw (ex-info (str "attempt to assign to const variable '" n "'")
                            {:type :error :line (or (:line var-node) stmt-line)}))
            (= wc :allow)
            nil
            (strict-globals? scopes)
            (throw (ex-info (str "variable '" n "' is not declared")
                            {:type :error :line (or (:line var-node) stmt-line)}))))))))

;; ============================================================================
;; Function body helper
;; ============================================================================

(defn- extract-func-params
  "Extract [param-name-strings vararg-name-or-nil] from a :func-body node.
   Mirrors the logic in expressions.clj eval-exp :function-def."
  [func-body]
  (let [param-list (:params func-body)]
    (if param-list
      (let [params (:params param-list)
            vararg-node (some #(when (= :vararg (:type %)) %) params)
            name-params (filter #(not= :vararg (:type %)) params)
            names (cond
                    (and (= 1 (count name-params))
                         (= :name-list (:type (first name-params))))
                    (mapv :value (:names (first name-params)))

                    (seq name-params)
                    (mapv :value name-params)

                    :else [])]
        [names (:name vararg-node)])
      [[] nil])))

(defn- check-func-body
  "Check a function body.  Outer-scopes is the scope stack at the point where
   the function is defined (const-info crosses closure boundaries)."
  [outer-scopes func-body]
  (let [[params vararg-name] (extract-func-params func-body)
        inner-scopes (push-scope outer-scopes)
        inner-scopes (reduce #(declare-local %1 %2 false) inner-scopes params)
        inner-scopes (if vararg-name
                       (declare-local inner-scopes vararg-name true)
                       inner-scopes)]
    (check-block inner-scopes (-> func-body :body :statements))))

;; ============================================================================
;; Block / statement walker
;; ============================================================================

(defn check-block
  "Walk a sequence of statements, threading the scope stack through.
   Returns the updated scope stack after all declarations in this block."
  [scopes stmts]
  (reduce check-stmt scopes stmts))

(defn check-stmt
  "Check one statement.  Returns updated scope stack."
  [scopes stmt]
  (if-not (map? stmt)
    scopes
    (case (:type stmt)

      ;; local [<const>/<close>] declarations
      ;; global declarations
      :global-none
      (set-strict-globals scopes)

      :global-wildcard
      (let [attrib (:attrib stmt)]
        (when (= :close attrib)
          (throw (ex-info "global variable cannot be to-be-closed"
                          {:type :error :line (:line stmt)})))
        (set-wildcard scopes (if (= :const attrib) :const :allow)))

      :global-decl
      (let [name-nodes (-> stmt :names :names)
            has-env? (some #(= "_ENV" (:value %)) name-nodes)]
        (if has-env?
          ;; _ENV in a global declaration activates strict mode and voids the statement.
          ;; This matches Lua 5.5: subsequent undeclared-global accesses (e.g. a = 10)
          ;; then produce "variable 'X' is not declared" compile-time errors.
          (set-strict-globals scopes)
          ;; Normal case: validate attributes and declare each name.
          (do
            (doseq [n name-nodes]
              (let [a (:attrib n)]
                (when (= a :close)
                  (throw (ex-info (str "global variable cannot be to-be-closed")
                                  {:type :error :line (:line n)})))
                (when (and a (not= a :const))
                  (throw (ex-info (str "unknown attribute '" (clojure.core/name a) "'")
                                  {:type :error :line (:line n)})))))
            (doseq [v (some-> stmt :values :values)] (check-exp scopes v))
            ;; declare-global per-name with per-name const? flag
            (reduce (fn [ss n]
                      (declare-global ss (:value n) (= :const (:attrib n))))
                    scopes name-nodes))))

      ;; local [<const>/<close>] declarations
      :local
      (let [name-nodes (-> stmt :names :names)]
        ;; Validate attribute names — only :const and :close are recognized
        (doseq [n name-nodes]
          (when-let [a (:attrib n)]
            (when-not (#{:const :close} a)
              (throw (ex-info (str "unknown attribute '" (name a) "'")
                              {:type :error :line (:line n)})))))
        ;; Validate to-be-closed multiplicity: at most one <close> per declaration
        (let [close-count (count (filter #(= :close (:attrib %)) name-nodes))]
          (when (> close-count 1)
            (throw (ex-info "multiple to-be-closed variables in local list"
                            {:type :error :line (:line stmt)}))))
        ;; Check RHS expressions in the current (pre-declaration) scope
        (doseq [v (some-> stmt :values :values)] (check-exp scopes v))
        ;; Declare each name; <const> and <close> are both read-only
        (reduce (fn [ss n]
                  (declare-local ss (:value n)
                                 (contains? #{:const :close} (:attrib n))))
                scopes name-nodes))

      ;; local function f() ... end
      ;; The name itself is non-const; function body gets its own param scope.
      :local-func-def
      (let [scopes (declare-local scopes (:value (:name stmt)) false)]
        (check-func-body scopes (:body stmt))
        scopes)

      ;; function f() ... end  (or  function t.f() ... end)
      ;; A simple name target (no dots/colon) is an assignment to that name —
      ;; check if it's const.  Method/field targets (f.x, f:m) are not const-checked.
      :func-def-stat
      (let [func-name (:name stmt)
            names (:names func-name)
            simple? (and (= 1 (count names)) (not (:method? func-name)))]
        (when simple?
          (check-assign-target scopes (first names) (:line stmt)))
        (check-func-body scopes (:body stmt))
        scopes)

      ;; global function f() ... end
      ;; Declares f as a global (regular, not const) and defines the function body.
      ;; `global function f` is a declaration — wildcards don't block it.
      ;; Only an existing explicit global<const> declaration prevents redefinition.
      :global-func-def
      (let [func-name (:name stmt)
            names (:names func-name)
            simple? (and (= 1 (count names)) (not (:method? func-name)))]
        (when simple?
          (when (= :global-const (lookup-var scopes (:value (first names))))
            (throw (ex-info (str "attempt to assign to const variable '" (:value (first names)) "'")
                            {:type :error :line (:line stmt)}))))
        (check-func-body scopes (:body stmt))
        (if simple?
          (declare-global scopes (:value (first names)) false)
          scopes))

      ;; x, y = expr, expr
      :assignment
      (do (doseq [v (-> stmt :vars :vars)] (check-assign-target scopes v (:line stmt)))
          (doseq [v (some-> stmt :values :values)] (check-exp scopes v))
          scopes)

      ;; do ... end
      :do
      (do (check-block (push-scope scopes) (-> stmt :body :statements)) scopes)

      ;; while cond do ... end
      :while
      (do (check-exp scopes (:condition stmt))
          (check-block (push-scope scopes) (-> stmt :body :statements))
          scopes)

      ;; repeat ... until cond
      :repeat
      (do (check-block (push-scope scopes) (-> stmt :body :statements))
          scopes)

      ;; if cond then ... [elseif ...] [else ...] end
      :if
      (do (check-exp scopes (:condition stmt))
          (check-block (push-scope scopes) (-> stmt :then :statements))
          (doseq [ei (:elseifs stmt)]
            (check-exp scopes (:condition ei))
            (check-block (push-scope scopes) (-> ei :body :statements)))
          (when (:else stmt)
            (check-block (push-scope scopes) (-> stmt :else :statements)))
          scopes)

      ;; for i = start, stop [, step] do ... end
      ;; Lua 5.5: the control variable is implicitly <const>.
      :for-numeric
      (do (check-exp scopes (:start stmt))
          (check-exp scopes (:end stmt))
          (when (:step stmt) (check-exp scopes (:step stmt)))
          (let [inner (declare-local (push-scope scopes) (:value (:var stmt)) true)]
            (check-block inner (-> stmt :body :statements)))
          scopes)

      ;; for k, v in expr do ... end
      ;; Lua 5.5: only the FIRST iteration variable (the control variable, checked
      ;; against nil to detect loop end) is implicitly <const>.  Subsequent variables
      ;; are regular locals and may be reassigned inside the loop body.
      :for-generic
      (do (doseq [v (some-> stmt :expressions :values)] (check-exp scopes v))
          (let [name-nodes (-> stmt :names :names)
                inner (reduce-kv (fn [ss idx n]
                                   (declare-local ss (:value n) (= 0 (long idx))))
                                 (push-scope scopes)
                                 (vec name-nodes))]
            (check-block inner (-> stmt :body :statements)))
          scopes)

      ;; return expr, ...
      :return
      (do (doseq [v (some-> stmt :values :values)] (check-exp scopes v)) scopes)

      ;; goto/label: the target/label name is NOT a variable reference; skip entirely.
      :goto scopes
      :label scopes

      ;; Everything else (break, function-call statement) — no declarations;
      ;; just walk sub-expressions for nested function defs.
      (do (check-exp scopes stmt) scopes))))

;; ============================================================================
;; Expression walker — only cares about nested function definitions
;; ============================================================================

(defn check-exp
  "Walk an expression node looking for nested function definitions.
   Also enforces undeclared-global reading."
  [scopes node]
  (when (map? node)
    (case (:type node)
      :name
      (let [n (:value node)
            status (lookup-var scopes n)]
        (when (= status :not-found)
          ;; Wildcard modes (:allow, :const) permit reading undeclared globals.
          ;; Only strict-globals (no wildcard) makes undeclared reads an error.
          ;; _ENV and _G are always accessible (pre-declared Lua pseudo-globals).
          (when (and (strict-globals? scopes)
                     (nil? (active-wildcard scopes))
                     (not (#{"_ENV" "_G"} n)))
            (throw (ex-info (str "variable '" n "' is not declared")
                            {:type :error :line (:line node)})))))

      :function-def
      (check-func-body scopes (:body node))

      ;; Field access: t.field — only visit the base object, not the field name.
      ;; The field name is a static key, not a variable reference.
      :field-access
      (check-exp scopes (:object node))

      ;; Method call: obj:method(args) — visit object and args but not the method name.
      :method-call
      (do (check-exp scopes (:object node))
          (doseq [v (some-> node :args :values)] (check-exp scopes v)))

      ;; For all other nodes, recursively visit child maps/sequences
      (doseq [v (vals node)]
        (cond
          (map? v)
          (check-exp scopes v)

          (sequential? v)
          (doseq [item v]
            (when (map? item) (check-exp scopes item))))))))

;; ============================================================================
;; Entry point
;; ============================================================================

(defn check!
  "Run the const-variable check on a fully-transformed CLua AST.
   Throws ex-info with {:type :error :line N} on the first violation found.
   Called from parser/parse-and-transform before returning the AST."
  [ast]
  (let [stmts (-> ast :body first :statements)]
    (check-block [{}] stmts)
    nil))
