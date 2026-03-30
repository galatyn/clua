(ns clua.interpreter.stack-machine
  "Explicit stack machine for precise coroutine resumption.

  Instead of using the JVM call stack, we maintain an explicit stack
  data structure that represents the execution state. This allows us to:

  1. Save exact execution position (expression-level, not just statement)
  2. Resume precisely after yield without re-executing sub-expressions
  3. Support proper coroutines with no re-evaluation issues

  Stack Frame Structure:
  - :type - What operation (eval-exp, call-fn, eval-stmt, etc.)
  - :state - Where in the operation (start, waiting, done, etc.)
  - :node - AST node being processed
  - :env - Environment
  - :data - Operation-specific data (args, partial results, etc.)"
  (:require [clojure.string :as str]
            [clua.interpreter.coro-runtime :as coro]
            [clua.interpreter.env :as env]
            [clua.interpreter.expressions :as expr]
            [clua.interpreter.operators :as ops]
            [clua.interpreter.tables :as tables]
            [clua.interpreter.types :as types])
  (:import (clojure.lang ArityException ExceptionInfo)
           (java.util HashMap)))
(set! *warn-on-reflection* true)


;; Forward declaration for call-function (defined in core, wired up later)
(declare ^:dynamic *call-function*)

;; Maximum call depth, matching Lua's LUAI_MAXCCALLS.
;; When exceeded, "C stack overflow" is raised as a catchable Lua error.
(def ^:const max-call-depth 200)

;; Forward declarations for statement handling helpers (defined later in file)
(declare handle-local-stmt)
;; Forward declarations for loop frame constructors (defined later in file)
(declare make-while-frame make-for-numeric-frame make-for-generic-frame make-repeat-frame)
;; Forward declarations for pcall/xpcall stack-machine frame helpers (defined near runner)
(declare lua-pcall? lua-xpcall? extract-lua-error apply-native-pcall-error
         recover-from-pcall)
;; Forward declarations for to-be-closed variable helpers (defined near recover-from-pcall)
(declare run-close-list! close-block-normal! close-for-backward-goto!)
;; Forward declaration for the inner error-recovery loop (defined with recover-from-pcall)
(declare recover-frames-loop)

(defn call-function-from-stack
  "Call a function from within the stack machine.
  This is a thin wrapper that delegates to the interpreter's call-function."
  [target args env]
  (if (bound? #'*call-function*)
    (*call-function* target args env)
    (throw (ex-info "call-function not bound - stack machine not properly integrated"
                    {:target target :args args}))))

(defn call-native-with-arity-retry
  "Call a native Clojure function, retrying with fewer args on ArityException.
   Lua silently ignores extra arguments to functions."
  [f args]
  (try
    (apply f args)
    (catch ArityException e
      (let [n (count args)
            msg (.getMessage e)]
        (if (and (> n 0) (.contains msg (str "(" n ")")))
          ((fn drop-extra [a]
             (if (empty? a)
               (throw (ex-info msg {:type :error}))
               (try
                 (apply f a)
                 (catch ArityException _
                   (drop-extra (vec (butlast a)))))))
           (vec (butlast args)))
          (throw (ex-info msg {:type :error})))))))

;;; Stack Frame Creation

(defn make-frame
  "Create a stack frame for an operation."
  [type state node env & {:as data}]
  (merge {:type type
          :state state
          :node node
          :env env}
         data))

(defn make-eval-exp-frame
  "Create a frame for evaluating an expression."
  [node env]
  (make-frame :eval-exp :start node env))

(defn make-call-frame
  "Create a frame for calling a function."
  [target args env]
  (make-frame :call-fn :eval-target nil env
              :target target
              :args args
              :results []))

(defn make-metamethod-call-frame
  "Create a frame for calling a metamethod.
  This allows the stack machine to manage the metamethod call/resume cycle."
  ([metamethod args env] (make-metamethod-call-frame metamethod args env nil))
  ([metamethod args env mm-name]
   (make-frame :metamethod-call :start nil env
               :metamethod metamethod
               :args args
               :mm-name mm-name
               :result nil)))

(defn- build-label-map
  "Scan block statements for :label nodes, return a map of label-name -> stmt-index."
  [statements]
  (reduce (fn [m [idx stmt]]
            (if (= :label (:type stmt))
              (assoc m (:value (:name stmt)) idx)
              m))
          {}
          (map-indexed vector statements)))

(defn make-block-frame
  "Create a frame for executing a block of statements.
  This allows Lua functions to execute entirely within the stack machine."
  [statements env]
  (make-frame :block :start nil env
              :statements statements
              :stmt-index 0
              :close-list []
              :close-list-ran? (atom false)))

(def ^:private close-call-node
  "Synthetic AST node for __close metamethod calls.
  Gives the call stack entry the name 'close'."
  {:type :function-call :target {:type :name :value "close"}})

(defn make-close-list-runner-frame
  "Create a frame for executing a close-list in the stack machine.
  items: collection of close items (LIFO order, already prepared by the block frame).
  initial-err: current error being propagated (nil for normal exit)."
  [items env initial-err]
  (make-frame :close-list-runner :scan nil env
              :items (vec items)
              :current-err initial-err))

(defn- make-error-propagation-frame
  "Create a frame for continuing error recovery after an async close-list runner completes.
  remaining: stack frames still to process for error recovery (below the closed block).
  self-close?: whether the original error was a coroutine.close() self-close error."
  [remaining self-close? env]
  (make-frame :error-propagation :await-runner nil env
              :remaining remaining
              :self-close? self-close?))

;;; Control Flow Signals
;;
;; Return and break signals are passed through the :result field to propagate
;; control flow across multiple stack frames without using exceptions.
;;
;; Signal format:
;;   {:signal :return :values v} - function return
;;   {:signal :break}            - break from loop

(defn make-return-signal [values] {:signal :return :values values})
(defn make-break-signal [] {:signal :break})
(defn make-goto-signal [label] {:signal :goto :label label})
(defn return-signal? [v] (and (map? v) (= :return (:signal v))))
(defn break-signal? [v] (and (map? v) (= :break (:signal v))))
(defn goto-signal? [v] (and (map? v) (= :goto (:signal v))))

(defn normalize-return-value
  "Normalize an exp-list result to a proper function return value.
  Single-element vectors are unwrapped; multi-value vectors are kept.
  Matches the normalization done by call-function."
  [v]
  (cond
    (and (vector? v) (= 1 (count v))) (first v)
    :else v))
(defn make-function-block-frame
  "Create a block frame marked as a function body.
  Function body blocks catch return signals and terminate the function."
  [statements env]
  (assoc (make-block-frame statements env) :function-body? true))

;;; Stack Operations

(defn push-frame
  "Push a frame onto the stack."
  [stack frame]
  (conj stack frame))

(defn pop-frame
  "Pop a frame from the stack. Returns [stack frame]."
  [stack]
  [(pop stack) (peek stack)])

(defn update-frame
  "Update the top frame with new values."
  [stack updates]
  (conj (pop stack) (merge (peek stack) updates)))

(defn- propagate-coroutine-env
  "When a Lua function's closure env differs from the calling frame's env
   (e.g. the function was defined in the main thread but is being called from
   a coroutine), copy coroutine-local atoms from the calling env into base-env
   so the callee shares the coroutine's call-stack, position tracking, and hook."
  [base-env calling-env]
  (let [ks [:call-stack :current-line :current-column :hook]]
    (reduce (fn [b k]
              (let [caller-val (get calling-env k)
                    base-val   (get b k)]
                (if (and caller-val (not= caller-val base-val))
                  (assoc b k caller-val)
                  b)))
            base-env
            ks)))

(defn set-frame-state
  "Update the state of the top frame."
  [stack new-state]
  (update-frame stack {:state new-state}))

(defn set-frame-result
  "Set the result on the top frame."
  [stack result]
  (update-frame stack {:result result}))

;;; Call Stack Tracking Helpers

(defn fire-hook!
  "Fire a debug hook event if a hook is registered and we are not already inside a hook.

   Events:
   - \"call\"   - fired after push-stack-frame! for a function entry
   - \"return\" - fired before pop-stack-frame! for a function exit
   - \"line\"   - fired before each new statement when the line changes
   - \"count\"  - fired every N statements (when count > 0)

   For call/return hooks, a synthetic frame for the hook function itself is
   pushed onto the call-stack so that debug.getinfo(2) inside the hook
   correctly returns the hooked function."
  [env event line-num]
  (when (and (bound? #'*call-function*) (not coro/*in-hook*))
    (when-let [hook-atom (:hook env)]
      (when-let [{hook-fn :fn mask :mask cnt :count
                  stepctr :stepctr lastline :lastline} @hook-atom]
        (let [should-fire?
              (case event
                "line"
                (when (str/includes? mask "l")
                  (let [last @lastline]
                    (when (not= last line-num)
                      (reset! lastline line-num)
                      true)))
                "call" (str/includes? mask "c")
                "tail call" (str/includes? mask "c")
                "return" (str/includes? mask "r")
                "count"
                (when (pos? (long cnt))
                  (let [c (aget ^longs stepctr 0)
                        nc (inc c)]
                    (if (>= nc (long cnt))
                      (do (aset ^longs stepctr 0 (long 0)) true)
                      (do (aset ^longs stepctr 0 (long nc)) false))))
                false)]
          (when should-fire?
            ;; Push a synthetic frame for the hook-fn so that inside the hook
            ;; debug.getinfo level-indexing sees: [..., hooked-fn, hook-fn, ...]
            (env/push-stack-frame! env nil line-num nil hook-fn nil 0 "hook")
            (try
              (binding [coro/*in-hook* true]
                (let [args (if (and (= event "line") (some? line-num))
                             [event line-num]
                             [event nil])]
                  (*call-function* hook-fn args env)))
              (finally
                (env/pop-stack-frame! env)))))))))

(defn- pop-call-stack-if-needed!
  "Pop the env call stack if this block frame pushed one (has :call-fn-env set).
   Fires the 'return' hook before popping, then restores the saved lastline so the
   caller's line-hook dedup sees the call-site line (not the callee's last line).
   When skip-return-hook? is true (tail-call TCO), the return hook is suppressed:
   PUC-Lua does not fire a return event for the frame being replaced by a tail call."
  ([frame] (pop-call-stack-if-needed! frame false))
  ([frame skip-return-hook?]
  (when-let [frame-env (:call-fn-env frame)]
    (when-not skip-return-hook? (fire-hook! frame-env "return" nil))
    ;; Restore lastline to pre-call value for correct caller-line dedup.
    ;; Mirrors PUC-Lua's per-activation-record line tracking.
    (when-let [saved (:saved-lastline frame)]
      (when-let [ha (:hook frame-env)]
        (when-let [la (:lastline @ha)]
          (reset! la saved))))
    (env/pop-stack-frame! frame-env))))

(defn- force-fire-line!
  "Reset the hook's lastline dedup to -1 and fire a line event at line-num.
   Forces the event to fire even if line-num equals the previously-fired line.
   Also updates the env's current-line position atom. No-op if line-num is nil."
  [env line-num]
  (when line-num
    (when-let [hook-atom (:hook env)]
      (when-let [la (:lastline @hook-atom)]
        (reset! la -1)))
    (env/set-position! env line-num nil)
    (fire-hook! env "line" line-num)))

(defn- fire-line!
  "Update env position to line-num and fire a line event (with normal lastline dedup).
   No-op if line-num is nil."
  [env line-num]
  (when line-num
    (env/set-position! env line-num nil)
    (fire-hook! env "line" line-num)))

;;; Expression Evaluation Handlers

(defmulti handle-eval-exp
  "Handle evaluation of an expression based on state.
  Dispatches on [node-type state] for eval-exp frames,
  or [frame-type state] for block/metamethod frames."
  (fn [_stack frame]
    (let [node (:node frame)]
      (if node
        ;; Regular eval-exp frame - dispatch on node type
        [(:type node) (:state frame)]
        ;; Block or metamethod frame - dispatch on frame type
        [(:type frame) (:state frame)]))))

;; Literal values - these are simple, just return the value
(defmethod handle-eval-exp [:nil :start] [stack _frame]
  ;; Pop this frame and set result on parent (or return if no parent)
  (let [[new-stack _] (pop-frame stack)]
    (if (empty? new-stack)
      [:done {:value nil}]
      [:continue (set-frame-result new-stack nil)])))

(defmethod handle-eval-exp [:boolean :start] [stack frame]
  (let [value (get-in frame [:node :value])
        [new-stack _] (pop-frame stack)]
    (if (empty? new-stack)
      [:done {:value value}]
      [:continue (set-frame-result new-stack value)])))

(defmethod handle-eval-exp [:number :start] [stack frame]
  (let [value (get-in frame [:node :value])
        [new-stack _] (pop-frame stack)]
    (if (empty? new-stack)
      [:done {:value value}]
      [:continue (set-frame-result new-stack value)])))

(defmethod handle-eval-exp [:string :start] [stack frame]
  (let [value (get-in frame [:node :value])
        [new-stack _] (pop-frame stack)]
    (if (empty? new-stack)
      [:done {:value value}]
      [:continue (set-frame-result new-stack value)])))

;; Function definition - create a Lua function object
(defmethod handle-eval-exp [:function-def :start] [stack frame]
  (let [node (:node frame)
        env (:env frame)
        func-body (:body node)
        param-list (:params func-body)
        ;; Extract parameter names and check for varargs
        [param-names has-varargs vararg-name]
        (if param-list
          (let [params (:params param-list)
                vararg-node (some #(when (= :vararg (:type %)) %) params)
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
            [names (boolean vararg-node) (:name vararg-node)])
          [[] false nil])
        lua-func {:type :lua-function
                  :params param-names
                  :varargs has-varargs
                  :vararg-name vararg-name
                  :body (:body func-body)
                  :env env
                  :line-defined (or (:line func-body) -1)
                  :last-line-defined (or (:last-line func-body) -1)}
        ;; Mark as yieldable if needed
        marked-func (coro/mark-yieldable lua-func)
        [new-stack _] (pop-frame stack)]
    (if (empty? new-stack)
      [:done {:value marked-func}]
      [:continue (set-frame-result new-stack marked-func)])))

;; Name lookup - variable references
(defmethod handle-eval-exp [:name :start] [stack frame]
  (let [var-name (get-in frame [:node :value])
        env (:env frame)
        value (env/lookup env var-name)
        [new-stack _] (pop-frame stack)]
    (if (empty? new-stack)
      [:done {:value value}]
      [:continue (set-frame-result new-stack value)])))

;; Vararg (...) - variable reference to varargs
(defmethod handle-eval-exp [:vararg :start] [stack frame]
  (let [env (:env frame)
        raw (env/lookup env "...")
        value (cond
                (and (map? raw) (:vararg-table raw))
                (expr/expand-vararg-table (:vararg-table raw))
                (vector? raw) raw
                :else [])
        [new-stack _] (pop-frame stack)]
    (if (empty? new-stack)
      [:done {:value value}]
      [:continue (set-frame-result new-stack value)])))

;; Parenthesized expression: (expr)
;; In Lua, (expr) truncates multiple values to exactly one.
;; State flow: :start -> :got-inner -> done (via :paren-unwrap)

(defmethod handle-eval-exp [:paren-exp :start] [stack frame]
  ;; Push a frame to evaluate the inner expression, then truncate result
  (let [inner-node (get-in frame [:node :expr])
        new-frame (update-frame stack {:state :paren-unwrap})
        inner-frame (make-eval-exp-frame inner-node (:env frame))]
    [:continue (push-frame new-frame inner-frame)]))

(defmethod handle-eval-exp [:paren-exp :paren-unwrap] [stack frame]
  ;; Inner expression evaluated - truncate to single value
  (let [raw-val (:result frame)
        ;; Truncate: if multi-value vector, take only first; if empty vector, use nil
        value (cond
                (and (vector? raw-val) (empty? raw-val)) nil
                (vector? raw-val) (first raw-val)
                :else raw-val)
        [new-stack _] (pop-frame stack)]
    (if (empty? new-stack)
      [:done {:value value}]
      [:continue (set-frame-result new-stack value)])))

;; Binary operations - need multi-state handling
;; State flow: :start -> :got-left -> :got-both -> done

(defmethod handle-eval-exp [:binary-exp :start] [stack frame]
  ;; Start: push frame to evaluate left operand
  (let [left-node (get-in frame [:node :left])
        new-frame (update-frame stack {:state :got-left})
        left-frame (make-eval-exp-frame left-node (:env frame))]
    [:continue (push-frame new-frame left-frame)]))

(defmethod handle-eval-exp [:binary-exp :got-left] [stack frame]
  ;; Left evaluated, result is on this frame
  ;; Short-circuit for and/or: may not need to evaluate right
  (let [left-val (types/unwrap-single (:result frame))
        op (get-in frame [:node :op])]
    (case op
      "and" (if (types/lua-truthy? left-val)
              ;; Truthy - need to evaluate right (right becomes the result)
              (let [right-node (get-in frame [:node :right])
                    new-frame (update-frame stack {:state :got-both
                                                   :left-val left-val
                                                   :result nil})
                    right-frame (make-eval-exp-frame right-node (:env frame))]
                [:continue (push-frame new-frame right-frame)])
              ;; Falsy - short-circuit, return left
              (let [[new-stack _] (pop-frame stack)]
                (if (empty? new-stack)
                  [:done {:value left-val}]
                  [:continue (set-frame-result new-stack left-val)])))
      "or" (if (types/lua-truthy? left-val)
             ;; Truthy - short-circuit, return left
             (let [[new-stack _] (pop-frame stack)]
               (if (empty? new-stack)
                 [:done {:value left-val}]
                 [:continue (set-frame-result new-stack left-val)]))
             ;; Falsy - need to evaluate right
             (let [right-node (get-in frame [:node :right])
                   new-frame (update-frame stack {:state :got-both
                                                  :left-val left-val
                                                  :result nil})
                   right-frame (make-eval-exp-frame right-node (:env frame))]
               [:continue (push-frame new-frame right-frame)]))
      ;; All other operators - evaluate right
      (let [right-node (get-in frame [:node :right])
            new-frame (update-frame stack {:state :got-both
                                           :left-val left-val
                                           :result nil})
            right-frame (make-eval-exp-frame right-node (:env frame))]
        [:continue (push-frame new-frame right-frame)]))))

(defmethod handle-eval-exp [:binary-exp :got-both] [stack frame]
  ;; Both operands evaluated - apply operation
  (let [left-val (:left-val frame)
        right-val (types/unwrap-single (:result frame))
        op (get-in frame [:node :op])
        env (:env frame)
        ;; Update position to operator's line so arithmetic errors report the right line
        _ (when-let [op-line (get-in frame [:node :op-line])]
            (env/set-position! env op-line nil nil))]
    (case op
      ;; and/or: right value is the result (short-circuit already resolved in :got-left)
      "and" (let [[new-stack _] (pop-frame stack)]
              (if (empty? new-stack)
                [:done {:value right-val}]
                [:continue (set-frame-result new-stack right-val)]))
      "or" (let [[new-stack _] (pop-frame stack)]
             (if (empty? new-stack)
               [:done {:value right-val}]
               [:continue (set-frame-result new-stack right-val)]))
      ;; All other operators: detect metamethod first, then compute or dispatch
      (try
        (let [mm-info (ops/find-binary-metamethod op left-val right-val)]
          (if mm-info
            ;; Metamethod path: run in stack machine so coroutine yields work correctly
            (let [post-proc (:post-process mm-info)
                  mm-fn (:fn mm-info)
                  mm-args (:args mm-info)
                  mm-name (or (tables/binary-metamethods op)
                              (get {"<" "__lt", "<=" "__le", ">" "__lt", ">=" "__le"
                                    "==" "__eq", "~=" "__eq"} op))
                  updated-stack (update-frame stack {:state :got-mm-result
                                                     :mm-post-process post-proc})
                  mm-frame (make-metamethod-call-frame mm-fn mm-args env mm-name)]
              [:continue (push-frame updated-stack mm-frame)])
            ;; Direct computation path (no metamethod needed)
            (let [result (ops/apply-binary-op op left-val right-val env)
                  [new-stack _] (pop-frame stack)]
              (if (empty? new-stack)
                [:done {:value result}]
                [:continue (set-frame-result new-stack result)]))))
        (catch ExceptionInfo e
          (let [data (ex-data e)]
            (if (= :error (:type data))
              (let [ctx (case op
                          ("+" "-" "*" "/" "//" "%" "^")
                          (cond
                            (nil? (ops/coerce-arith left-val)) (expr/operand-context-desc (get-in frame [:node :left]) env)
                            (nil? (ops/coerce-arith right-val)) (expr/operand-context-desc (get-in frame [:node :right]) env))
                          ("&" "|" "~" "<<" ">>")
                          (cond
                            (nil? (ops/coerce-bitwise left-val)) (expr/operand-context-desc (get-in frame [:node :left]) env)
                            (nil? (ops/coerce-bitwise right-val)) (expr/operand-context-desc (get-in frame [:node :right]) env))
                          nil)]
                (throw (ex-info (str (ex-message e) (or ctx "")) data)))
              (throw e))))))))

(defmethod handle-eval-exp [:binary-exp :got-mm-result] [stack frame]
  ;; Metamethod returned a result - apply post-processing and propagate
  (let [mm-result (:result frame)
        post-proc (:mm-post-process frame)
        final-val (post-proc mm-result)
        [new-stack _] (pop-frame stack)]
    (if (empty? new-stack)
      [:done {:value final-val}]
      [:continue (set-frame-result new-stack final-val)])))

;; Unary operations
;; State flow: :start -> :got-operand -> done

(defmethod handle-eval-exp [:unary-exp :start] [stack frame]
  ;; Start: push frame to evaluate operand
  (let [operand-node (get-in frame [:node :operand])
        new-frame (update-frame stack {:state :got-operand})
        operand-frame (make-eval-exp-frame operand-node (:env frame))]
    [:continue (push-frame new-frame operand-frame)]))

(defmethod handle-eval-exp [:unary-exp :got-operand] [stack frame]
  ;; Operand evaluated - apply unary operation
  (let [val (types/unwrap-single (:result frame))
        op (get-in frame [:node :op])
        env (:env frame)
        ;; Update position to operator's line so arithmetic errors report the right line
        _ (when-let [op-line (get-in frame [:node :op-line])]
            (env/set-position! env op-line nil nil))]
    (try
      (let [mm-info (ops/find-unary-metamethod op val)]
        (if mm-info
          ;; Metamethod path: run in stack machine so coroutine yields work correctly
          (let [post-proc (:post-process mm-info)
                mm-fn (:fn mm-info)
                mm-args (:args mm-info)
                mm-name (tables/unary-metamethods op)
                updated-stack (update-frame stack {:state :got-mm-result
                                                   :mm-post-process post-proc})
                mm-frame (make-metamethod-call-frame mm-fn mm-args env mm-name)]
            [:continue (push-frame updated-stack mm-frame)])
          ;; Direct computation path (no metamethod needed)
          (let [result (case op
                         "-" (if (number? val)
                               (if (integer? val)
                                 (unchecked-negate (long val))
                                 (- (double val)))
                               ;; Coercible string: find-unary-metamethod returned nil so coerce-arith succeeds
                               (let [coerced (ops/coerce-arith val)]
                                 (if (integer? coerced)
                                   (unchecked-negate (long coerced))
                                   (- (double coerced)))))
                         "not" (not (types/lua-truthy? val))
                         "#" (if (string? val)
                               (count val)
                               ;; Table without __len: find-unary-metamethod returned nil
                               (tables/table-sequence-len val))
                         "~" (bit-not (long (ops/coerce-bitwise val))))
                [new-stack _] (pop-frame stack)]
            (if (empty? new-stack)
              [:done {:value result}]
              [:continue (set-frame-result new-stack result)]))))
      (catch ExceptionInfo e
        (let [data (ex-data e)]
          (if (= :error (:type data))
            (throw (ex-info (str (ex-message e)
                                 (or (expr/operand-context-desc (get-in frame [:node :operand]) env) ""))
                            data))
            (throw e)))))))

(defmethod handle-eval-exp [:unary-exp :got-mm-result] [stack frame]
  ;; Metamethod returned a result - apply post-processing and propagate
  (let [mm-result (:result frame)
        post-proc (:mm-post-process frame)
        final-val (post-proc mm-result)
        [new-stack _] (pop-frame stack)]
    (if (empty? new-stack)
      [:done {:value final-val}]
      [:continue (set-frame-result new-stack final-val)])))

;; Field access - table.field
;; State flow: :start -> :got-object -> done

(defmethod handle-eval-exp [:field-access :start] [stack frame]
  ;; Start: push frame to evaluate object
  (let [object-node (get-in frame [:node :object])
        new-frame (update-frame stack {:state :got-object})
        object-frame (make-eval-exp-frame object-node (:env frame))]
    [:continue (push-frame new-frame object-frame)]))

(defmethod handle-eval-exp [:field-access :got-object] [stack frame]
  ;; Object evaluated - get field
  (let [object-val (:result frame)
        field-name (let [field (get-in frame [:node :field])]
                     (if (and (map? field) (= :name (:type field)))
                       (:value field)
                       field))
        env (:env frame)]
    (cond
      ;; nil object - error
      (nil? object-val)
      (throw (ex-info (str "attempt to index a nil value"
                           (expr/value-source-desc (get-in frame [:node :object]) env))
                      {:type :error}))

      (or (types/lua-table? object-val)
          (and (map? object-val) (:clua-metatable object-val))
          ;; Basic types (number, boolean) with type-level metatable
          (some? (tables/get-type-metatable object-val)))
      ;; Check if there's a direct value first (only for lua tables)
      (let [raw-value (when (types/lua-table? object-val)
                        (tables/table-get object-val field-name))]
        (if (some? raw-value)
          ;; Found value directly - return it
          (let [[new-stack _] (pop-frame stack)]
            (if (empty? new-stack)
              [:done {:value raw-value}]
              [:continue (set-frame-result new-stack raw-value)]))
          ;; No direct value - check for __index metamethod
          (if-let [index-mm (tables/get-metamethod object-val "__index")]
            (cond
              ;; __index is a table - recursive lookup
              (types/lua-table? index-mm)
              (let [result (tables/table-get-with-meta index-mm field-name env)
                    [new-stack _] (pop-frame stack)]
                (if (empty? new-stack)
                  [:done {:value result}]
                  [:continue (set-frame-result new-stack result)]))

              ;; __index is a function - use metamethod-call frame!
              (or (fn? index-mm) (= :lua-function (:type index-mm)))
              (let [;; Pop this frame and push metamethod-call frame
                    [new-stack _] (pop-frame stack)
                    metamethod-frame (make-metamethod-call-frame index-mm [object-val field-name] env "__index")]
                [:continue (push-frame new-stack metamethod-frame)])

              ;; __index is neither table nor function - error
              :else
              (throw (ex-info (str "attempt to index a " (tables/lua-type-name index-mm) " value")
                              {:type :error})))
            ;; No __index metamethod
            (let [[new-stack _] (pop-frame stack)]
              (if (empty? new-stack)
                [:done {:value nil}]
                [:continue (set-frame-result new-stack nil)])))))

      ;; Not a table, userdata, or basic type with metatable - error
      :else
      (throw (ex-info (str "attempt to index a " (tables/lua-type-name object-val) " value"
                           (expr/value-source-desc (get-in frame [:node :object]) env))
                      {:type :error})))))

;; Index access - table[key]
;; State flow: :start -> :got-object -> :got-key -> done

(defmethod handle-eval-exp [:index-access :start] [stack frame]
  ;; Start: push frame to evaluate object
  (let [object-node (get-in frame [:node :object])
        new-frame (update-frame stack {:state :got-object})
        object-frame (make-eval-exp-frame object-node (:env frame))]
    [:continue (push-frame new-frame object-frame)]))

(defmethod handle-eval-exp [:index-access :got-object] [stack frame]
  ;; Object evaluated, now evaluate key
  (let [object-val (:result frame)
        key-node (or (get-in frame [:node :index]) (get-in frame [:node :key]))
        new-frame (update-frame stack {:state :got-key
                                       :object-val object-val
                                       :result nil})
        key-frame (make-eval-exp-frame key-node (:env frame))]
    [:continue (push-frame new-frame key-frame)]))

(defmethod handle-eval-exp [:index-access :got-key] [stack frame]
  ;; Both object and key evaluated - get value
  (let [object-val (:object-val frame)
        key-val (types/unwrap-single (:result frame))
        env (:env frame)]
    (cond
      ;; nil object - error
      (nil? object-val)
      (throw (ex-info (str "attempt to index a nil value"
                           (expr/value-source-desc (get-in frame [:node :object]) env))
                      {:type :error}))

      (or (types/lua-table? object-val)
          (and (map? object-val) (:clua-metatable object-val))
          ;; Basic types (number, boolean) with type-level metatable
          (some? (tables/get-type-metatable object-val)))
      ;; Check if there's a direct value first (only for lua tables)
      (let [raw-value (when (types/lua-table? object-val)
                        (tables/table-get object-val key-val))]
        (if (some? raw-value)
          ;; Found value directly - return it
          (let [[new-stack _] (pop-frame stack)]
            (if (empty? new-stack)
              [:done {:value raw-value}]
              [:continue (set-frame-result new-stack raw-value)]))
          ;; No direct value - check for __index metamethod
          (if-let [index-mm (tables/get-metamethod object-val "__index")]
            (cond
              ;; __index is a table - recursive lookup
              (types/lua-table? index-mm)
              (let [result (tables/table-get-with-meta index-mm key-val env)
                    [new-stack _] (pop-frame stack)]
                (if (empty? new-stack)
                  [:done {:value result}]
                  [:continue (set-frame-result new-stack result)]))

              ;; __index is a function - use metamethod-call frame!
              (or (fn? index-mm) (= :lua-function (:type index-mm)))
              (let [;; Pop this frame and push metamethod-call frame
                    [new-stack _] (pop-frame stack)
                    metamethod-frame (make-metamethod-call-frame index-mm [object-val key-val] env "__index")]
                [:continue (push-frame new-stack metamethod-frame)])

              ;; __index is neither table nor function - error
              :else
              (throw (ex-info (str "attempt to index a " (tables/lua-type-name index-mm) " value")
                              {:type :error})))
            ;; No __index metamethod
            (let [[new-stack _] (pop-frame stack)]
              (if (empty? new-stack)
                [:done {:value nil}]
                [:continue (set-frame-result new-stack nil)])))))

      ;; Not a table, userdata, or basic type with metatable - error
      :else
      (throw (ex-info (str "attempt to index a " (tables/lua-type-name object-val) " value"
                           (expr/value-source-desc (get-in frame [:node :object]) env))
                      {:type :error})))))

;; Function calls - most complex operation
;; State flow: :start -> :eval-target -> :eval-args -> :call -> done

(defn- extract-arg-nodes
  "Extract actual argument AST nodes from an args node.
  The parser wraps args in {:type :args :values [{:type :exp-list :values [...]}]}.
  This function unwraps that structure to get individual argument nodes."
  [args-node]
  (cond
    (and (map? args-node) (= :args (:type args-node)))
    (let [vs (:values args-node)]
      ;; Unwrap single exp-list wrapper produced by the parser
      (if (and (= 1 (count vs))
               (= :exp-list (:type (first vs))))
        (:values (first vs))
        vs))
    (vector? args-node) args-node
    :else []))

(defmethod handle-eval-exp [:function-call :start] [stack frame]
  ;; Start: push frame to evaluate target function
  (let [target-node (get-in frame [:node :target])
        args-node (get-in frame [:node :args])
        args-nodes (extract-arg-nodes args-node)
        new-frame (update-frame stack {:state :eval-target
                                       :args-nodes args-nodes
                                       :arg-vals []})
        target-frame (make-eval-exp-frame target-node (:env frame))]
    [:continue (push-frame new-frame target-frame)]))

(defmethod handle-eval-exp [:function-call :eval-target] [stack frame]
  ;; Target evaluated - now evaluate arguments one by one
  (let [target-val (:result frame)
        args-nodes (:args-nodes frame)
        arg-vals (:arg-vals frame)]
    (if (empty? args-nodes)
      ;; No arguments - go straight to call
      [:continue (update-frame stack {:state :call
                                      :target-val target-val
                                      :result nil})]
      ;; Evaluate first argument
      (let [first-arg (first args-nodes)
            rest-args (rest args-nodes)
            new-frame (update-frame stack {:state :eval-args
                                           :target-val target-val
                                           :args-nodes rest-args
                                           :current-arg-node first-arg
                                           :arg-vals arg-vals
                                           :result nil})
            arg-frame (make-eval-exp-frame first-arg (:env frame))]
        [:continue (push-frame new-frame arg-frame)]))))

(defmethod handle-eval-exp [:function-call :eval-args] [stack frame]
  ;; One argument evaluated - add to list and continue
  (let [arg-val (:result frame)
        current-arg-node (:current-arg-node frame)
        arg-vals (:arg-vals frame)
        args-nodes (:args-nodes frame)]
    (if (empty? args-nodes)
      ;; Last argument - spread if multi-value expression, otherwise just add
      (let [new-arg-vals (if (and (types/is-multi-value-expr? current-arg-node)
                                  (vector? arg-val))
                           (into arg-vals arg-val)
                           (conj arg-vals arg-val))]
        [:continue (update-frame stack {:state :call
                                        :arg-vals new-arg-vals
                                        :current-arg-node nil
                                        :result nil})])
      ;; Non-last argument - unwrap to single value and continue
      (let [single-val (types/unwrap-single arg-val)
            new-arg-vals (conj arg-vals single-val)
            next-arg (first args-nodes)
            rest-args (rest args-nodes)
            new-frame (update-frame stack {:state :eval-args
                                           :arg-vals new-arg-vals
                                           :current-arg-node next-arg
                                           :args-nodes rest-args
                                           :result nil})
            arg-frame (make-eval-exp-frame next-arg (:env frame))]
        [:continue (push-frame new-frame arg-frame)]))))

(defmethod handle-eval-exp [:function-call :call] [stack frame]
  ;; All parts evaluated - now call the function
  (let [;; Unwrap multi-value return used as callee: Lua uses only the first value
        target-val (let [tv (:target-val frame)] (if (vector? tv) (first tv) tv))
        arg-vals (:arg-vals frame)
        env (:env frame)
        node (:node frame)
        fn-name (when node (expr/get-call-name (:target node)))
        fn-namewhat (when node (expr/get-call-namewhat (:target node) env))
        fn-line (when node (:line node))
        fn-col (when node (:column node))
        ;; extraargs: number of extra table args prepended by __call chain dispatch
        extraargs (:call-chain-depth frame 0)
        ;; is-tail-call: true when this call was reached via TCO (eval-exp frame marked)
        is-tail-call (:is-tail-call frame false)]
    ;; Call depth limit: mirrors Lua's LUAI_MAXCCALLS.
    ;; Thrown as catchable ExceptionInfo so pcall/xpcall can intercept it.
    (when (>= (count @(:call-stack env)) max-call-depth)
      (throw (ex-info "C stack overflow" {:type :error})))
    (cond
      ;; Lua function - execute in stack machine!
      (= :lua-function (:type target-val))
      (let [;; Set up function environment
            outer-scope-count (count (:scopes (:env target-val)))
            base-env (propagate-coroutine-env
                       (-> (env/push-scope (:env target-val))
                           (assoc :outer-scope-count outer-scope-count))
                       env)
            fn-joins (env/get-upvalue-joins target-val)
            func-env (if fn-joins (assoc base-env :upvalue-joins fn-joins) base-env)
            params (:params target-val)
            has-varargs (:varargs target-val)
            vararg-name (:vararg-name target-val)
            num-params (count params)
            ;; Bind parameters (missing args become nil, matching Lua semantics)
            _ (doseq [[param-name arg-val] (map vector params (concat arg-vals (repeat nil)))]
                (env/define! func-env param-name arg-val))
            ;; Bind varargs if needed
            _ (when has-varargs
                (let [varargs (vec (drop num-params arg-vals))]
                  (if vararg-name
                    (let [vt (tables/make-table)]
                      (tables/table-set! vt "n" (count varargs))
                      (dorun (map-indexed (fn [i v] (tables/table-set! vt (unchecked-inc (long i)) v)) varargs))
                      (env/define! func-env vararg-name vt)
                      (env/define! func-env "..." {:vararg-table vt}))
                    (env/define! func-env "..." varargs))))
            ;; Get function body statements
            body-block (:body target-val)
            statements (:statements body-block)
            ;; Pop this function-call frame and push function-body block frame
            [new-stack _] (pop-frame stack)
            ;; env-atom is updated before each statement so debug.getlocal(level>1) works
            env-atom (atom func-env)
            ;; Push call stack frame for stack traces and getlocal
            _ (env/push-stack-frame! func-env fn-name fn-line fn-col target-val env-atom extraargs fn-namewhat is-tail-call)
            _ (fire-hook! func-env (if is-tail-call "tail call" "call") nil)
            ;; Mark block frame with call-fn-env so it pops the frame on exit
            ;; Store func-end-line for implicit return line hook (PUC-Lua fires at 'end' line)
            func-end (when-let [ll (:last-line-defined target-val)]
                       (when (pos? (long ll)) ll))
            ;; Save and reset lastline so the called function fires fresh line events.
            ;; On return, we restore lastline so the caller's dedup sees the call-site line.
            ;; This mirrors PUC-Lua's per-activation-record line tracking.
            saved-lastline (when-let [ha (:hook func-env)]
                             (when-let [la (:lastline @ha)] @la))
            _ (when-let [ha (:hook func-env)]
                (when-let [la (:lastline @ha)] (reset! la -1)))
            block-frame (assoc (make-function-block-frame statements func-env)
                          :call-fn-env func-env
                          :frame-env-atom env-atom
                          :func-end-line func-end
                          :saved-lastline saved-lastline)]
        [:continue (push-frame new-stack block-frame)])

      ;; pcall: intercept and convert to a :pcall-frame for proper yield support.
      ;; The frame runs the body as stack machine sub-frames so coroutine yields
      ;; inside the body propagate through the saved stack correctly.
      ;; Push a call stack frame for pcall so debug.getinfo sees it during __close.
      (lua-pcall? target-val)
      (let [body-fn (first arg-vals)
            body-args (vec (rest arg-vals))
            [new-stack _] (pop-frame stack)
            _ (env/push-stack-frame! env (or fn-name "pcall") fn-line fn-col target-val nil)
            pcall-f {:type :pcall-frame :state :run-body
                     :body-fn body-fn :body-args body-args
                     :outer-wrap nil :msgh nil :env env
                     :pcall-call-env env}]
        [:continue (push-frame new-stack pcall-f)])

      ;; xpcall: intercept and convert to a :pcall-frame for proper yield support.
      ;; xpcall(pcall, handler, real-body, ...): unwrap the nested pcall so we run
      ;; real-body directly with combined pcall+xpcall error semantics (:xpcall-pcall).
      ;; xpcall(lua-fn, handler, args...): run lua-fn with xpcall error semantics (:xpcall).
      (lua-xpcall? target-val)
      (let [fn-arg (first arg-vals)
            msgh (second arg-vals)
            fn-extra-args (vec (drop 2 arg-vals))
            [new-stack _] (pop-frame stack)]
        (if (lua-pcall? fn-arg)
          ;; xpcall(pcall, handler, real-body, extra-args...)
          (let [real-body (first fn-extra-args)
                real-body-args (vec (rest fn-extra-args))
                pcall-f {:type :pcall-frame :state :run-body
                         :body-fn real-body :body-args real-body-args
                         :outer-wrap :xpcall-pcall :msgh msgh :env env}]
            [:continue (push-frame new-stack pcall-f)])
          ;; xpcall(any-fn, handler, args...)
          (let [pcall-f {:type :pcall-frame :state :run-body
                         :body-fn fn-arg :body-args fn-extra-args
                         :outer-wrap :xpcall :msgh msgh :env env}]
            [:continue (push-frame new-stack pcall-f)])))

      ;; Native Clojure function - call directly
      (fn? target-val)
      (do
        (env/push-stack-frame! env fn-name fn-line fn-col target-val nil extraargs fn-namewhat is-tail-call)
        ;; Skip "call" hook when resuming past a yield: the native function is being
        ;; re-called to retrieve resume values (coroutine.yield detects resume-values-set
        ;; and returns them instead of yielding again). The "call" hook already fired on
        ;; the original call before the yield.
        (let [resuming-past-yield? (when-let [cc (coro/get-current-coroutine)]
                                     (contains? @(:state cc) :resume-values-set))]
          (when-not resuming-past-yield? (fire-hook! env (if is-tail-call "tail call" "call") nil)))
        ;; Restore position to the call site before invoking native function.
        ;; Argument evaluation (e.g. nested function calls) may have updated the
        ;; shared atom so errors inside the native function report the right line.
        (when fn-line (env/set-position! env fn-line fn-col))
        (let [yield-caught (volatile! false)
              raw-result (try
                           ;; Rebind *current-env* to frame env so native fns see the
                           ;; correct :source for error() level-based location prefix.
                           (binding [env/*current-env* env]
                             (call-native-with-arity-retry target-val arg-vals))
                           (catch ExceptionInfo e
                             ;; Set flag before finally so "return" hook is suppressed for yield.
                             (when (= :coro-yield (:type (ex-data e)))
                               (vreset! yield-caught true))
                             (throw e))
                           (finally
                             (when-not @yield-caught (fire-hook! env "return" nil))
                             (env/pop-stack-frame! env)))
              result (expr/maybe-convert-result raw-result env)
              [new-stack _] (pop-frame stack)]
          (if (empty? new-stack)
            [:done {:value result}]
            [:continue (set-frame-result new-stack result)])))

      ;; Callable table via __call metamethod - dispatch natively in the stack machine.
      ;; This avoids JVM recursion for __call chains and enables TCO through __call.
      ;; Frame type must be :eval-exp (not :function-call) so run-stack-machine routes
      ;; it through handle-eval-exp-with-yield; dispatch is on node type = :function-call.
      (and (types/lua-table? target-val) (tables/get-metamethod target-val "__call"))
      (let [mm (tables/get-metamethod target-val "__call")
            mm-args (vec (cons target-val arg-vals))
            chain-depth (unchecked-inc (long (:call-chain-depth frame 0)))
            [new-stack _] (pop-frame stack)
            ;; Replace this call frame with a new eval-exp frame at :call state.
            ;; If mm is itself a table with __call, this handler will run again.
            ;; :call-chain-depth tracks depth for debug.getinfo extraargs and overflow.
            call-frame (make-frame :eval-exp :call node env
                                   :target-val mm :arg-vals mm-args
                                   :call-chain-depth chain-depth)]
        [:continue (push-frame new-stack call-frame)])

      ;; Other callable types - use old system
      :else
      (try
        (let [result (call-function-from-stack target-val arg-vals env)
              [new-stack _] (pop-frame stack)]
          (if (empty? new-stack)
            [:done {:value result}]
            [:continue (set-frame-result new-stack result)]))
        (catch ExceptionInfo e
          (if (= :coro-yield (:type (ex-data e)))
            [:yield {:values (:values (ex-data e))
                     :stack stack}]
            (if (= :call-error (:type (ex-data e)))
              (let [ctx (when node (expr/operand-context-desc (:target node) env))]
                (throw (ex-info (str (ex-message e) (or ctx "")) (ex-data e))))
              (throw e))))))))

;; Method calls - object:method(args)
;; State flow: :start -> :got-object -> :eval-args -> :call -> done

(defmethod handle-eval-exp [:method-call :start] [stack frame]
  ;; Start: push frame to evaluate object expression
  (let [object-node (get-in frame [:node :object])
        new-frame (update-frame stack {:state :got-object})
        object-frame (make-eval-exp-frame object-node (:env frame))]
    [:continue (push-frame new-frame object-frame)]))

(defmethod handle-eval-exp [:method-call :got-object] [stack frame]
  ;; Object evaluated - look up method and prepare args
  (let [obj (:result frame)
        method-name (get-in frame [:node :method :value])
        env (:env frame)
        ;; Guard: non-indexable objects fail with an index error before method lookup
        _ (when (or (nil? obj)
                    (and (not (types/lua-table? obj))
                         (not (string? obj))
                         (not (and (map? obj) (:clua-metatable obj)))))
            (throw (ex-info (str "attempt to index a " (tables/lua-type-name obj) " value"
                                 (or (expr/operand-context-desc (get-in frame [:node :object]) env) ""))
                            {:type :error})))
        ;; Look up method using metatable-aware lookup
        method (cond
                 (types/lua-table? obj)
                 (tables/table-get-with-meta obj method-name env)
                 ;; Userdata (file handles etc.) with :clua-metatable
                 (and (map? obj) (:clua-metatable obj))
                 (tables/table-get-with-meta obj method-name env)
                 ;; String method calls (s:reverse(), s:sub(), etc.)
                 (string? obj)
                 (when-let [string-lib (env/lookup env "string")]
                   (tables/table-get string-lib method-name))
                 :else nil)
        ;; Extract argument nodes (unwrap exp-list wrapper)
        args-node (get-in frame [:node :args])
        args-nodes (extract-arg-nodes args-node)]
    (if (empty? args-nodes)
      ;; No arguments - go straight to call
      [:continue (update-frame stack {:state :call
                                      :object-val obj
                                      :method-val method
                                      :arg-vals []
                                      :result nil})]
      ;; Evaluate first argument
      (let [first-arg (first args-nodes)
            rest-args (rest args-nodes)
            new-frame (update-frame stack {:state :eval-args
                                           :object-val obj
                                           :method-val method
                                           :args-nodes rest-args
                                           :current-arg-node first-arg
                                           :arg-vals []
                                           :result nil})
            arg-frame (make-eval-exp-frame first-arg (:env frame))]
        [:continue (push-frame new-frame arg-frame)]))))

(defmethod handle-eval-exp [:method-call :eval-args] [stack frame]
  ;; One argument evaluated - add to list and continue
  (let [arg-val (:result frame)
        current-arg-node (:current-arg-node frame)
        arg-vals (:arg-vals frame)
        args-nodes (:args-nodes frame)]
    (if (empty? args-nodes)
      ;; Last argument - spread if multi-value expression, otherwise just add
      (let [new-arg-vals (if (and (types/is-multi-value-expr? current-arg-node)
                                  (vector? arg-val))
                           (into arg-vals arg-val)
                           (conj arg-vals arg-val))]
        [:continue (update-frame stack {:state :call
                                        :arg-vals new-arg-vals
                                        :current-arg-node nil
                                        :result nil})])
      ;; Non-last argument - unwrap to single value and continue
      (let [single-val (types/unwrap-single arg-val)
            new-arg-vals (conj arg-vals single-val)
            next-arg (first args-nodes)
            rest-args (rest args-nodes)
            new-frame (update-frame stack {:state :eval-args
                                           :arg-vals new-arg-vals
                                           :current-arg-node next-arg
                                           :args-nodes rest-args
                                           :result nil})
            arg-frame (make-eval-exp-frame next-arg (:env frame))]
        [:continue (push-frame new-frame arg-frame)]))))

(defmethod handle-eval-exp [:method-call :call] [stack frame]
  ;; All parts evaluated - call method with object as first arg (self)
  (let [obj (:object-val frame)
        method (:method-val frame)
        arg-vals (:arg-vals frame)
        env (:env frame)
        node (:node frame)
        method-name (get-in frame [:node :method :value])
        obj-name (when node (expr/get-call-name (:object node)))
        fn-name (str (or obj-name "?") ":" method-name)
        fn-line (when node (:line node))
        fn-col (when node (:column node))
        ;; Prepend object as self parameter
        all-args (cons obj arg-vals)
        is-tail-call (:is-tail-call frame false)]
    (cond
      ;; Lua function - execute in stack machine
      (= :lua-function (:type method))
      (let [method-joins (env/get-upvalue-joins method)
            outer-scope-count (count (:scopes (:env method)))
            base-method-env (propagate-coroutine-env
                              (assoc (env/push-scope (:env method))
                                :outer-scope-count outer-scope-count)
                              env)
            func-env (if method-joins (assoc base-method-env :upvalue-joins method-joins) base-method-env)
            params (:params method)
            has-varargs (:varargs method)
            vararg-name (:vararg-name method)
            num-params (count params)
            _ (doseq [[param-name arg-val] (map vector params (concat all-args (repeat nil)))]
                (env/define! func-env param-name arg-val))
            _ (when has-varargs
                (let [varargs (vec (drop num-params all-args))]
                  (if vararg-name
                    (let [vt (tables/make-table)]
                      (tables/table-set! vt "n" (count varargs))
                      (dorun (map-indexed (fn [i v] (tables/table-set! vt (unchecked-inc (long i)) v)) varargs))
                      (env/define! func-env vararg-name vt)
                      (env/define! func-env "..." {:vararg-table vt}))
                    (env/define! func-env "..." varargs))))
            body-block (:body method)
            statements (:statements body-block)
            [new-stack _] (pop-frame stack)
            env-atom (atom func-env)
            _ (env/push-stack-frame! func-env fn-name fn-line fn-col method env-atom 0 "method" is-tail-call)
            _ (fire-hook! func-env (if is-tail-call "tail call" "call") nil)
            func-end (when-let [ll (:last-line-defined method)]
                       (when (pos? (long ll)) ll))
            saved-lastline (when-let [ha (:hook func-env)]
                             (when-let [la (:lastline @ha)] @la))
            _ (when-let [ha (:hook func-env)]
                (when-let [la (:lastline @ha)] (reset! la -1)))
            block-frame (assoc (make-function-block-frame statements func-env)
                          :call-fn-env func-env
                          :frame-env-atom env-atom
                          :func-end-line func-end
                          :saved-lastline saved-lastline)]
        [:continue (push-frame new-stack block-frame)])

      ;; Native Clojure function - call directly
      (fn? method)
      (do
        (env/push-stack-frame! env fn-name fn-line fn-col method nil 0 "method" is-tail-call)
        (let [resuming-past-yield? (when-let [cc (coro/get-current-coroutine)]
                                     (contains? @(:state cc) :resume-values-set))]
          (when-not resuming-past-yield? (fire-hook! env (if is-tail-call "tail call" "call") nil)))
        (let [yield-caught (volatile! false)
              raw-result (try
                           ;; Rebind *current-env* to frame env and set *in-method-call*
                           ;; so native fns can distinguish method vs direct call context.
                           (binding [env/*current-env* env
                                     env/*in-method-call* true]
                             (call-native-with-arity-retry method all-args))
                           (catch ExceptionInfo e
                             (when (= :coro-yield (:type (ex-data e)))
                               (vreset! yield-caught true))
                             (throw e))
                           (finally
                             (when-not @yield-caught (fire-hook! env "return" nil))
                             (env/pop-stack-frame! env)))
              result (expr/maybe-convert-result raw-result env)
              [new-stack _] (pop-frame stack)]
          (if (empty? new-stack)
            [:done {:value result}]
            [:continue (set-frame-result new-stack result)])))

      ;; Other callable types - use old system
      :else
      (try
        (let [result (call-function-from-stack method (vec all-args) env)
              [new-stack _] (pop-frame stack)]
          (if (empty? new-stack)
            [:done {:value result}]
            [:continue (set-frame-result new-stack result)]))
        (catch ExceptionInfo e
          (if (= :coro-yield (:type (ex-data e)))
            [:yield {:values (:values (ex-data e))
                     :stack stack}]
            (if (= :call-error (:type (ex-data e)))
              (throw (ex-info (str (ex-message e) " (method '" method-name "')") (ex-data e)))
              (throw e))))))))

;; Table constructors - {fields...}
;; State flow: :start -> :eval-fields -> :got-field-key -> :got-field-value -> (loop) -> done

(defn- flatten-table-fields
  "Normalize the parser's field structure into a flat vector of field nodes."
  [raw-fields]
  (if (and (seq raw-fields)
           (vector? (first raw-fields))
           (not (keyword? (first (first raw-fields)))))
    ;; Fields are nested: [[{...} [:fieldsep] {...}]] -> flatten and filter
    (->> (first raw-fields)
         (filter #(and (map? %) (:type %)))
         vec)
    ;; Fields are flat: [{...} {...}]
    (vec raw-fields)))

(defmethod handle-eval-exp [:table :start] [stack frame]
  ;; Create table, prepare fields, start evaluating
  (let [env (:env frame)
        table (tables/make-table env)
        raw-fields (get-in frame [:node :fields])
        fields (flatten-table-fields raw-fields)]
    [:continue (update-frame stack {:state :eval-fields
                                    :table table
                                    :fields fields
                                    :field-index 0
                                    :array-idx 1})]))

(defmethod handle-eval-exp [:table :eval-fields] [stack frame]
  ;; Process next field or finish
  (let [fields (:fields frame)
        field-index (:field-index frame)
        env (:env frame)]
    (if (>= (long field-index) (count fields))
      ;; All fields processed - return the table
      (let [table (:table frame)
            [new-stack _] (pop-frame stack)]
        (if (empty? new-stack)
          [:done {:value table}]
          [:continue (set-frame-result new-stack table)]))
      ;; Process current field
      (let [field (nth fields field-index)
            field-type (:type field)
            is-last (= field-index (dec (count fields)))]
        (case field-type
          :array-field
          ;; Evaluate value, go to :got-field-value
          (let [new-frame (update-frame stack {:state :got-field-value
                                               :field-kind :array
                                               :is-last-field is-last
                                               :current-value-node (:value field)
                                               :result nil})
                val-frame (make-eval-exp-frame (:value field) env)]
            [:continue (push-frame new-frame val-frame)])

          :bracket-field
          ;; Evaluate key first, then value
          (let [new-frame (update-frame stack {:state :got-field-key
                                               :field-kind :bracket
                                               :is-last-field is-last
                                               :field-value-node (:value field)
                                               :result nil})
                key-frame (make-eval-exp-frame (:key field) env)]
            [:continue (push-frame new-frame key-frame)])

          :name-field
          ;; Key is a string literal, just evaluate value
          (let [key-str (:value (:name field))
                new-frame (update-frame stack {:state :got-field-value
                                               :field-kind :named
                                               :field-key key-str
                                               :is-last-field is-last
                                               :result nil})
                val-frame (make-eval-exp-frame (:value field) env)]
            [:continue (push-frame new-frame val-frame)])

          :field
          ;; Key may be a name (string) or expression
          (let [key-node (:key field)]
            (if (= :name (:type key-node))
              ;; Name key - use string directly, just evaluate value
              (let [new-frame (update-frame stack {:state :got-field-value
                                                   :field-kind :named
                                                   :field-key (:value key-node)
                                                   :is-last-field is-last
                                                   :result nil})
                    val-frame (make-eval-exp-frame (:value field) env)]
                [:continue (push-frame new-frame val-frame)])
              ;; Expression key - evaluate key first
              (let [new-frame (update-frame stack {:state :got-field-key
                                                   :field-kind :field
                                                   :is-last-field is-last
                                                   :field-value-node (:value field)
                                                   :result nil})
                    key-frame (make-eval-exp-frame key-node env)]
                [:continue (push-frame new-frame key-frame)]))))))))

(defmethod handle-eval-exp [:table :got-field-key] [stack frame]
  ;; Key evaluated - save it, now evaluate value
  (let [key-val (:result frame)
        value-node (:field-value-node frame)
        env (:env frame)
        new-frame (update-frame stack {:state :got-field-value
                                       :field-key key-val
                                       :result nil})
        val-frame (make-eval-exp-frame value-node env)]
    [:continue (push-frame new-frame val-frame)]))

(defmethod handle-eval-exp [:table :got-field-value] [stack frame]
  ;; Value evaluated - apply field to table, advance to next field
  (let [val (:result frame)
        table (:table frame)
        field-kind (:field-kind frame)
        array-idx (:array-idx frame)
        env (:env frame)
        is-last (:is-last-field frame)
        current-value-node (:current-value-node frame)
        ;; Update table and array-idx based on field kind
        new-array-idx
        (case field-kind
          :array
          (if (and is-last current-value-node
                   (types/is-multi-value-expr? current-value-node)
                   (vector? val))
            ;; Multi-value spread for last array field
            (do (doseq [[i v] (map-indexed vector val)]
                  (tables/table-set! table (unchecked-add (long array-idx) (long i)) v env))
                (unchecked-add (long array-idx) (count val)))
            ;; Single value
            (do (tables/table-set! table array-idx val env)
                (unchecked-inc (long array-idx))))

          (:bracket :field)
          (let [key-val (:field-key frame)]
            (tables/table-set! table key-val val env)
            array-idx)

          :named
          (let [key-val (:field-key frame)]
            (tables/table-set! table key-val val env)
            array-idx))]
    [:continue (update-frame stack {:state :eval-fields
                                    :field-index (unchecked-inc (long (:field-index frame)))
                                    :array-idx new-array-idx
                                    :field-kind nil
                                    :field-key nil
                                    :field-value-node nil
                                    :current-value-node nil
                                    :is-last-field nil
                                    :result nil})]))

;; Expression list - for return statements with multiple values
;; State flow: :start -> :eval-init -> :eval-last -> done
;; Track: :init-vals (values of all but last expr), :remaining (exprs to evaluate)

(defmethod handle-eval-exp [:exp-list :start] [stack frame]
  (let [values-nodes (get-in frame [:node :values])]
    (if (empty? values-nodes)
      ;; Empty list - return empty vector
      (let [[new-stack _] (pop-frame stack)]
        (if (empty? new-stack)
          [:done {:value []}]
          [:continue (set-frame-result new-stack [])]))
      ;; Has values - evaluate all but last for single values
      (if (= 1 (count values-nodes))
        ;; Only one value - go straight to eval-last
        [:continue (update-frame stack {:state :eval-last
                                        :init-vals []
                                        :last-node (first values-nodes)})]
        ;; Multiple values - evaluate init values first
        (let [init-nodes (butlast values-nodes)
              first-init (first init-nodes)
              rest-init (rest init-nodes)
              last-node (last values-nodes)
              new-frame (update-frame stack {:state :eval-init
                                             :init-vals []
                                             :remaining rest-init
                                             :last-node last-node})
              init-frame (make-eval-exp-frame first-init (:env frame))]
          [:continue (push-frame new-frame init-frame)])))))

(defmethod handle-eval-exp [:exp-list :eval-init] [stack frame]
  ;; One init value evaluated - add to list
  (let [val (:result frame)
        ;; Unwrap if vector (take only first value for init expressions)
        single-val (if (vector? val) (first val) val)
        init-vals (:init-vals frame)
        new-init-vals (conj init-vals single-val)
        remaining (:remaining frame)]
    (if (empty? remaining)
      ;; All init values done - move to eval-last
      [:continue (update-frame stack {:state :eval-last
                                      :init-vals new-init-vals
                                      :result nil})]
      ;; More init values to evaluate
      (let [next-node (first remaining)
            rest-remaining (rest remaining)
            new-frame (update-frame stack {:state :eval-init
                                           :init-vals new-init-vals
                                           :remaining rest-remaining
                                           :result nil})
            next-frame (make-eval-exp-frame next-node (:env frame))]
        [:continue (push-frame new-frame next-frame)]))))

(defmethod handle-eval-exp [:exp-list :eval-last] [stack frame]
  ;; Need to evaluate the last expression
  (let [init-vals (:init-vals frame)
        last-node (:last-node frame)]
    (if last-node
      ;; Evaluate last expression
      (let [new-frame (update-frame stack {:state :got-last
                                           :init-vals init-vals
                                           :result nil})
            last-frame (make-eval-exp-frame last-node (:env frame))]
        [:continue (push-frame new-frame last-frame)])
      ;; No last node (shouldn't happen, but handle it)
      (let [[new-stack _] (pop-frame stack)
            result init-vals]
        (if (empty? new-stack)
          [:done {:value result}]
          [:continue (set-frame-result new-stack result)])))))

(defmethod handle-eval-exp [:exp-list :got-last] [stack frame]
  ;; Last expression evaluated - combine with init values
  (let [init-vals (:init-vals frame)
        last-val (:result frame)
        last-node (:last-node frame)
        ;; Check if last expression is multi-value and result is vector
        is-multi-value? (and (map? last-node)
                             (types/is-multi-value-expr? last-node)
                             (vector? last-val))
        ;; Combine results
        result (if is-multi-value?
                 (into init-vals last-val)
                 (conj init-vals last-val))
        [new-stack _] (pop-frame stack)]
    (if (empty? new-stack)
      [:done {:value result}]
      [:continue (set-frame-result new-stack result)])))

;; Metamethod call - special frame type for calling metamethods
;; This allows the stack machine to manage metamethod yields/resumes
;; State flow: :start -> :calling -> done

(defmethod handle-eval-exp [:metamethod-call :start] [stack _frame]
  ;; About to call metamethod - transition to :calling state
  [:continue (update-frame stack {:state :calling})])

(defmethod handle-eval-exp [:metamethod-call :calling] [stack frame]
  ;; Call the metamethod
  (let [metamethod (:metamethod frame)
        args (:args frame)]
    (cond
      ;; Lua function - execute in stack machine!
      (= :lua-function (:type metamethod))
      (let [;; Set up function environment
            func-env (env/push-scope (:env metamethod))
            params (:params metamethod)
            has-varargs (:varargs metamethod)
            vararg-name (:vararg-name metamethod)
            num-params (count params)
            ;; Bind parameters (missing args become nil, matching Lua semantics)
            _ (doseq [[param-name arg-val] (map vector params (concat args (repeat nil)))]
                (env/define! func-env param-name arg-val))
            ;; Bind varargs if needed
            _ (when has-varargs
                (let [varargs (vec (drop num-params args))]
                  (if vararg-name
                    (let [vt (tables/make-table)]
                      (tables/table-set! vt "n" (count varargs))
                      (dorun (map-indexed (fn [i v] (tables/table-set! vt (unchecked-inc (long i)) v)) varargs))
                      (env/define! func-env vararg-name vt)
                      (env/define! func-env "..." {:vararg-table vt}))
                    (env/define! func-env "..." varargs))))
            ;; Get function body statements
            body-block (:body metamethod)
            statements (:statements body-block)
            ;; Pop this metamethod-call frame and push function-body block frame
            [new-stack _] (pop-frame stack)
            ;; Push call-stack frame so debug.getinfo sees namewhat="metamethod" inside the fn.
            ;; Strip "__" prefix from metamethod name for the display name.
            mm-raw (:mm-name frame)
            mm-display (when mm-raw (if (str/starts-with? mm-raw "__") (subs mm-raw 2) mm-raw))
            env-atom (atom func-env)
            _ (env/push-stack-frame! func-env mm-display nil nil metamethod env-atom 0 "metamethod")
            _ (fire-hook! func-env "call" nil)
            ;; Save and reset lastline so the called fn fires fresh line events on return.
            saved-lastline (when-let [ha (:hook func-env)]
                             (when-let [la (:lastline @ha)] @la))
            _ (when-let [ha (:hook func-env)]
                (when-let [la (:lastline @ha)] (reset! la -1)))
            block-frame (assoc (make-function-block-frame statements func-env)
                          :call-fn-env func-env
                          :frame-env-atom env-atom
                          :saved-lastline saved-lastline)]
        [:continue (push-frame new-stack block-frame)])

      ;; Native Clojure function - call directly
      (fn? metamethod)
      (let [result (apply metamethod args)
            ;; Unwrap vector results
            final-value (if (vector? result) (first result) result)
            [new-stack _] (pop-frame stack)]
        (if (empty? new-stack)
          [:done {:value final-value}]
          [:continue (set-frame-result new-stack final-value)]))

      ;; Other callable types - error
      :else
      (let [mm-name (:mm-name frame)
            type-str (tables/lua-type-name metamethod)
            base-msg (str "attempt to call a " type-str " value")]
        (throw (ex-info (if mm-name
                          (str base-msg " (metamethod '" (subs mm-name 2) "')")
                          base-msg)
                        {:type :error}))))))

;; Block execution - for Lua function bodies
;; State flow: :start -> :executing -> done
;; Executes statements one by one


(defmethod handle-eval-exp [:block :start] [stack frame]
  ;; Build label-map for goto jumps, then start executing
  (let [label-map (build-label-map (:statements frame))]
    [:continue (update-frame stack {:state :executing :label-map label-map})]))

(defmethod handle-eval-exp [:block :executing] [stack frame]
  ;; Execute statements one by one using native stack machine evaluation
  (let [statements (:statements frame)
        stmt-index (:stmt-index frame)
        env (:env frame)
        is-function-body (:function-body? frame)]
    (if (>= (long stmt-index) (count statements))
      ;; All statements executed - block complete.
      ;; Function bodies return [] (zero values) when they fall off the end.
      ;; Sub-blocks and top-level chunks return nil (no signal).
      ;; For non-function sub-blocks, propagate the final env to the parent
      ;; frame as :body-env.  The repeat-until loop uses :body-env to evaluate
      ;; its condition in the scope of the loop body (Lua spec), which must
      ;; include any per-local-scope pushes that happened during the body.
      (let [close-list (:close-list frame)
            ran? (:close-list-ran? frame)
            completion-val (if is-function-body [] nil)]
        (if (seq close-list)
          ;; Has close items - mark as ran, push runner, transition to :closing
          (do
            (when ran? (reset! ran? true))
            (let [runner (make-close-list-runner-frame close-list env nil)
                  updated-block (update-frame stack {:state :closing
                                                     :pending {:type :fall-off
                                                               :completion-val completion-val}})]
              [:continue (push-frame updated-block runner)]))
          ;; No close items - complete immediately
          (let [_ (when ran? (reset! ran? true))
                _ (when (and is-function-body (:func-end-line frame))
                    (fire-line! env (:func-end-line frame)))
                _ (pop-call-stack-if-needed! frame)
                [new-stack _] (pop-frame stack)]
            (if (empty? new-stack)
              [:done {:value completion-val}]
              [:continue (-> (if is-function-body
                               new-stack
                               (update-frame new-stack {:body-env env}))
                             (set-frame-result completion-val))]))))
      ;; Execute next statement - dispatch based on type
      (let [stmt (nth statements stmt-index)
            stmt-type (:type stmt)
            _ (env/increment-steps! env)
            _ (expr/update-position! stmt env)
            ;; Update frame-env-atom so debug.getlocal(level>1) sees current scope
            _ (when-let [ea (:frame-env-atom frame)] (reset! ea env))
            ;; Fire line hook when the source line changes, then count hook.
            ;; For-loops, if, and local-func-def suppress the generic fire and
            ;; handle their own hook firing (for-loops reset lastline for forced
            ;; per-iteration fires; if fires at condition line; local-func-def
            ;; fires at the funcbody end-line; do suppresses entirely).
            _ (when-not (#{:if :do :for-numeric :for-generic :local-func-def :repeat :while} stmt-type)
                (when-let [line-atom (:current-line env)]
                  (when-let [line-num @line-atom]
                    (fire-hook! env "line" line-num))))
            _ (fire-hook! env "count" nil)]
        (case stmt-type
          ;; Expression statement - evaluate and discard result
          (:function-call :method-call)
          (let [updated-block (update-frame stack {:state :eval-stmt})
                expr-frame (make-eval-exp-frame stmt env)]
            [:continue (push-frame updated-block expr-frame)])

          ;; Return statement
          :return
          (let [exp-list (:values stmt)
                values-list (and exp-list (:values exp-list))]
            (cond
              ;; Empty return - returns zero values ([] not nil)
              (or (nil? exp-list) (empty? values-list))
              (let [close-list (:close-list frame)
                    ran? (:close-list-ran? frame)]
                (if (seq close-list)
                  (do
                    (when ran? (reset! ran? true))
                    (let [runner (make-close-list-runner-frame close-list env nil)
                          updated-block (update-frame stack {:state :closing
                                                             :pending {:type :empty-return}})]
                      [:continue (push-frame updated-block runner)]))
                  (let [_ (when ran? (reset! ran? true))
                        [new-stack _] (pop-frame stack)
                        _ (pop-call-stack-if-needed! frame)]
                    (cond
                      (empty? new-stack) [:done {:value []}]
                      is-function-body [:continue (set-frame-result new-stack [])]
                      :else [:continue (set-frame-result new-stack (make-return-signal []))]))))

              ;; TAIL CALL OPTIMIZATION:
              ;; Return exactly one function/method call in a function body.
              ;; Pop this block frame and push the call directly, eliminating
              ;; the :eval-return waiting frame for O(1) stack depth.
              ;; Only applies when there are NO to-be-closed variables in scope:
              ;; per Lua spec, a call cannot be a tail call if tbc variables are active
              ;; (they must close AFTER the called function returns, not before it runs).
              (and is-function-body
                   (= 1 (count values-list))
                   (#{:function-call :method-call} (:type (first values-list)))
                   (empty? (:close-list frame)))
              (let [call-node (first values-list)
                    ran? (:close-list-ran? frame)
                    _ (when ran? (reset! ran? true))
                    [new-stack _] (pop-frame stack)
                    _ (pop-call-stack-if-needed! frame true)]
                [:continue (push-frame new-stack (assoc (make-eval-exp-frame call-node env) :is-tail-call true))])

              ;; EXTENDED TAIL CALL OPTIMIZATION for tail-position sub-blocks.
              ;; A sub-block returning a single function call can be treated as a
              ;; tail call if all ancestor frames up to the enclosing function body
              ;; are pass-through blocks (:await-substmt state, not function-body),
              ;; AND none of the blocks being popped have to-be-closed variables
              ;; (Lua spec: calls cannot be tail in the scope of tbc variables).
              ;; This handles: function f() if cond then return g() end end
              ;; and arbitrarily deep nesting of if/do/etc. blocks.
              (and (not is-function-body)
                   (= 1 (count values-list))
                   (#{:function-call :method-call} (:type (first values-list)))
                   (empty? (:close-list frame)))
              (let [call-node (first values-list)
                    tail-pos (loop [s (pop stack) intermediates []]
                               (when-not (empty? s)
                                 (let [pf (peek s)]
                                   (cond
                                     (and (= :block (:type pf)) (:function-body? pf)
                                          (empty? (:close-list pf)))
                                     {:outer-stack (pop s) :func-frame pf :intermediates intermediates}
                                     (and (= :block (:type pf)) (= :await-substmt (:state pf))
                                          (empty? (:close-list pf)))
                                     (recur (pop s) (conj intermediates pf))
                                     :else nil))))]
                (if tail-pos
                  (let [{:keys [outer-stack func-frame intermediates]} tail-pos
                        _ (close-block-normal! frame env)
                        _ (doseq [f intermediates] (close-block-normal! f (:env f)))
                        _ (close-block-normal! func-frame (:env func-frame))
                        _ (pop-call-stack-if-needed! func-frame true)]
                    [:continue (push-frame outer-stack (assoc (make-eval-exp-frame call-node env) :is-tail-call true))])
                  (let [updated-block (update-frame stack {:state :eval-return})
                        expr-frame (make-eval-exp-frame exp-list env)]
                    [:continue (push-frame updated-block expr-frame)])))

              ;; Regular return - evaluate exp-list and handle in :eval-return
              :else
              (let [updated-block (update-frame stack {:state :eval-return})
                    expr-frame (make-eval-exp-frame exp-list env)]
                [:continue (push-frame updated-block expr-frame)])))

          ;; Local declaration
          :local
          (handle-local-stmt stack stmt env)

          ;; If statement: fire at condition line (not if-keyword line), store end-line
          :if
          (let [cond-node (:condition stmt)
                end-line (:end-line stmt)
                cond-line (or (:line cond-node) (:op-line cond-node) (:line stmt))
                _ (when cond-line (fire-line! env cond-line))
                updated-block (update-frame stack {:state :eval-if-cond
                                                   :if-stmt stmt
                                                   :pending-end-line end-line})
                cond-frame (make-eval-exp-frame cond-node env)]
            [:continue (push-frame updated-block cond-frame)])

          ;; Do block
          :do
          (let [body-block (:body stmt)
                sub-statements (:statements body-block)
                sub-env (env/push-scope env)
                sub-block (make-block-frame sub-statements sub-env)
                updated-block (update-frame stack {:state :await-substmt})]
            [:continue (push-frame updated-block sub-block)])

          ;; Break statement - emit break signal
          :break
          (let [_ (close-block-normal! frame env)
                [new-stack _] (pop-frame stack)]
            (if (empty? new-stack)
              [:done {:value nil}]
              [:continue (set-frame-result new-stack (make-break-signal))]))

          ;; While loop
          :while
          (let [while-frm (make-while-frame stmt env)
                updated-block (update-frame stack {:state :await-substmt})]
            [:continue (push-frame updated-block while-frm)])

          ;; For-numeric loop
          :for-numeric
          (let [for-frm (make-for-numeric-frame stmt env)
                updated-block (update-frame stack {:state :await-substmt})]
            [:continue (push-frame updated-block for-frm)])

          ;; For-generic loop
          :for-generic
          (let [for-frm (make-for-generic-frame stmt env)
                updated-block (update-frame stack {:state :await-substmt})]
            [:continue (push-frame updated-block for-frm)])

          ;; Repeat loop
          :repeat
          (let [repeat-frm (make-repeat-frame stmt env)
                updated-block (update-frame stack {:state :await-substmt})]
            [:continue (push-frame updated-block repeat-frm)])

          ;; No-op, label, bare name, and nil-type (raw parse tokens like [[:label]])
          (nil :nop :label :name :global-wildcard :global-none)
          [:continue (update-frame stack {:stmt-index (unchecked-inc (long stmt-index))})]

          ;; Global declaration: global x = 1
          :global-decl
          (let [name-nodes (-> stmt :names :names)
                values-exp (:values stmt)]
            ;; Redefinition check only applies when an initializer is present.
            ;; A bare 'global X' declaration (without '= value') is always allowed.
            ;; When a local _ENV table is in scope, that table IS the effective
            ;; global environment, so we check it for existing definitions.
            (when (and values-exp (seq (:values values-exp)))
              (let [reversed-scopes (reverse (:scopes env))
                    local-env-tbl (some (fn [^HashMap s]
                                          (when (.containsKey s "_ENV") (.get s "_ENV")))
                                        reversed-scopes)]
                (doseq [name-node name-nodes]
                  (let [name-str (:value name-node)
                        global-val (if (and local-env-tbl (= :lua-table (:type local-env-tbl)))
                                     (tables/table-get local-env-tbl name-str)
                                     (env/lookup (assoc env :scopes []) name-str))]
                    (when-not (nil? global-val)
                      (throw (ex-info (str "global '" name-str "' already defined")
                                      {:type :error :line (:line name-node)})))))))
            (if (or (nil? values-exp) (empty? (:values values-exp)))
              ;; No initialization - mark as global-redirect only if inside local scopes.
              ;; At the top level (no local scopes) the name is already global; no marker needed.
              (do
                (when (seq (:scopes env))
                  (doseq [name-node name-nodes]
                    (env/define! env (:value name-node) env/global-ref-marker)))
                [:continue (update-frame stack {:stmt-index (unchecked-inc (long stmt-index))})])
              ;; Has values - evaluate expression list first, then bind in new state
              (let [updated-block (update-frame stack {:state :eval-global-decl
                                                       :global-names (mapv :value name-nodes)})
                    expr-frame (make-eval-exp-frame values-exp env)]
                [:continue (push-frame updated-block expr-frame)])))

          ;; Goto statement - jump to label within block or emit signal to parent
          :goto
          (let [label-name (:value (:label stmt))
                label-map (:label-map frame)]
            (if-let [target-idx (get label-map label-name)]
              (if (< (long target-idx) (long stmt-index))
                ;; Backward goto: call __close and undeclare <close> vars that go out of scope
                (let [new-close-list (close-for-backward-goto! (:close-list frame) target-idx env)]
                  [:continue (update-frame stack {:stmt-index target-idx :close-list new-close-list})])
                ;; Forward goto within block - parser already validated no local crossing
                [:continue (update-frame stack {:stmt-index target-idx})])
              ;; Label not in this block - run close-list and propagate goto-signal upward
              (let [_ (close-block-normal! frame env)
                    [new-stack _] (pop-frame stack)]
                (if (empty? new-stack)
                  [:done {:value nil}]
                  [:continue (set-frame-result new-stack (make-goto-signal label-name))]))))

          ;; Global named function: global function name() ... end
          ;; Creates a global-ref-marker in the current scope (if any) so that the name
          ;; resolves to the global env, then assigns the function to that global.
          :global-func-def
          (let [fname (:name stmt)
                fbody (:body stmt)
                func-value (expr/eval-exp {:type :function-def :body fbody} env)
                names (:names fname)
                func-name (:value (last names))
                func-with-name (assoc func-value :name func-name)]
            (when (and (= 1 (count names)) (seq (:scopes env)))
              (env/define! env (:value (first names)) env/global-ref-marker))
            (env/assign! env (:value (last names)) func-with-name)
            [:continue (update-frame stack {:stmt-index (unchecked-inc (long stmt-index))})])

          ;; Named function definition: function name() ... end
          :func-def-stat
          (let [fname (:name stmt)
                fbody (:body stmt)
                fbody-with-self (if (:method? fname)
                                  (update-in fbody [:params :params 0 :names]
                                             (fn [names]
                                               (vec (cons {:type :name :value "self"} names))))
                                  fbody)
                func-value (expr/eval-exp {:type :function-def :body fbody-with-self} env)
                names (:names fname)
                func-name (:value (last names))
                func-with-name (assoc func-value :name func-name)]
            (if (= 1 (count names))
              (env/assign! env (:value (first names)) func-with-name)
              (let [table-names (butlast names)
                    field-name (:value (last names))
                    target-table (reduce
                                   (fn [tbl name-node]
                                     (let [key (:value name-node)
                                           next-tbl (if (types/lua-table? tbl)
                                                      (tables/table-get-with-meta tbl key env)
                                                      (env/lookup env key))]
                                       (when-not (and next-tbl (types/lua-table? next-tbl))
                                         (throw (ex-info (str "attempt to index a non-table value (field '" key "')")
                                                         {:type :error})))
                                       next-tbl))
                                   nil
                                   table-names)]
                (tables/table-set-with-meta! target-table field-name func-with-name env)))
            [:continue (update-frame stack {:stmt-index (unchecked-inc (long stmt-index))})])

          ;; Local function definition: local function name() ... end
          ;; PUC-Lua fires the line event at the 'end' line (CLOSURE instruction position),
          ;; not at the 'local function' keyword line.
          :local-func-def
          (let [name (:value (:name stmt))
                fbody (:body stmt)
                func-value (expr/eval-exp {:type :function-def :body fbody} env)
                func-with-name (assoc func-value :name name)
                last-line (:last-line fbody)]
            (env/define! env name func-with-name)
            (when last-line (fire-line! env last-line))
            [:continue (update-frame stack {:stmt-index (unchecked-inc (long stmt-index))})])

          ;; Assignment: a, b = expr1, expr2
          :assignment
          (let [vars (:vars (:vars stmt))
                values-node (:values stmt)]
            (if (or (nil? values-node) (empty? (:values values-node)))
              ;; No RHS - assign all vars to nil
              (do
                (doseq [var-node vars]
                  (case (:type var-node)
                    :name (env/assign! env (:value var-node) nil)
                    :index-access (let [tbl (expr/eval-exp (:object var-node) env)
                                        key (expr/eval-exp (:index var-node) env)]
                                    (try
                                      (tables/table-set-with-meta! tbl key nil env)
                                      (catch ExceptionInfo e
                                        (if (= :error (:type (ex-data e)))
                                          (let [ctx (expr/operand-context-desc (:object var-node) env)]
                                            (throw (ex-info (str (ex-message e) (or ctx "")) (ex-data e))))
                                          (throw e)))))
                    :field-access (let [tbl (expr/eval-exp (:object var-node) env)
                                        key (:value (:field var-node))]
                                    (try
                                      (tables/table-set-with-meta! tbl key nil env)
                                      (catch ExceptionInfo e
                                        (if (= :error (:type (ex-data e)))
                                          (let [ctx (expr/operand-context-desc (:object var-node) env)]
                                            (throw (ex-info (str (ex-message e) (or ctx "")) (ex-data e))))
                                          (throw e)))))))
                [:continue (update-frame stack {:stmt-index (unchecked-inc (long stmt-index))})])
              ;; Has RHS - evaluate exp-list via SM, then assign in :eval-assign-vars
              [:continue (push-frame (update-frame stack {:state :eval-assign-vars
                                                          :assign-vars vars})
                                     (make-eval-exp-frame values-node env))])))))))

(defmethod handle-eval-exp [:block :eval-stmt] [stack frame]
  ;; Expression statement completed, result is in :result
  ;; Discard result and move to next statement
  (let [stmt-index (:stmt-index frame)]
    [:continue (update-frame stack {:state :executing
                                    :stmt-index (unchecked-inc (long stmt-index))
                                    :result nil})]))

(defmethod handle-eval-exp [:block :eval-return] [stack frame]
  ;; Return expression evaluated, result is in :result.
  ;; Function body blocks return values directly; sub-blocks emit return signals.
  ;; Normalize the return value: single-element vectors are unwrapped to match
  ;; the behavior of call-function (which also normalizes return values).
  (let [return-value (normalize-return-value (:result frame))
        is-function-body (:function-body? frame)
        env (:env frame)
        close-list (:close-list frame)
        ran? (:close-list-ran? frame)]
    (if (seq close-list)
      ;; Has close items - stash return value, push runner
      (do
        (when ran? (reset! ran? true))
        (let [runner (make-close-list-runner-frame close-list env nil)
              updated-block (update-frame stack {:state :closing
                                                 :pending {:type :return
                                                           :return-value return-value}})]
          [:continue (push-frame updated-block runner)]))
      ;; No close items - complete immediately
      (let [[new-stack _] (pop-frame stack)]
        (cond
          (empty? new-stack)
          (do
            (pop-call-stack-if-needed! frame)
            [:done {:value return-value}])

          is-function-body
          (do
            (pop-call-stack-if-needed! frame)
            [:continue (set-frame-result new-stack return-value)])

          :else
          [:continue (set-frame-result new-stack (make-return-signal return-value))])))))

(defmethod handle-eval-exp [:block :closing] [stack frame]
  ;; The close-list runner just completed. (:result frame) is the final error or nil.
  ;; If error: throw it (will be caught by recover-from-pcall / outer error handling).
  ;; If nil: complete the block with its pending result.
  (let [close-err (:result frame)
        pending (:pending frame)
        env (:env frame)
        is-function-body (:function-body? frame)]
    (when close-err (throw close-err))
    ;; No close error - proceed with stashed pending result
    (let [_ (when (and is-function-body
                       (= :fall-off (:type pending))
                       (:func-end-line frame))
               (fire-line! env (:func-end-line frame)))
          _ (pop-call-stack-if-needed! frame)
          [new-stack _] (pop-frame stack)
          pending-type (:type pending)]
      (case pending-type
        :fall-off
        (let [completion-val (:completion-val pending)]
          (if (empty? new-stack)
            [:done {:value completion-val}]
            (if is-function-body
              [:continue (set-frame-result new-stack completion-val)]
              [:continue (-> (update-frame new-stack {:body-env env})
                             (set-frame-result completion-val))])))
        :empty-return
        (if (empty? new-stack)
          [:done {:value []}]
          (if is-function-body
            [:continue (set-frame-result new-stack [])]
            [:continue (set-frame-result new-stack (make-return-signal []))]))
        :return
        (let [return-value (:return-value pending)]
          (if (empty? new-stack)
            [:done {:value return-value}]
            (if is-function-body
              [:continue (set-frame-result new-stack return-value)]
              [:continue (set-frame-result new-stack (make-return-signal return-value))])))
))))

;; Helper functions for statement handling

(defn handle-local-stmt [stack stmt env]
  ;; Local declaration: local name = value
  ;; Note: (:names stmt) is a name-list map {:type :name-list :names [...]},
  ;; so we need (-> stmt :names :names) to get the actual name nodes vector.
  ;;
  ;; Each local declaration pushes a fresh scope so that closures created
  ;; across goto-loop iterations get distinct upvalue cells (required for
  ;; debug.upvalueid to work correctly).
  (let [name-nodes (-> stmt :names :names)
        values-exp (:values stmt)
        frame (peek stack)
        stmt-index (:stmt-index frame)]
    (if (or (nil? values-exp) (empty? (:values values-exp)))
      ;; No initialization - push new scope and bind all names to nil
      (let [new-env (env/push-scope env)]
        (doseq [name-node name-nodes]
          (env/define! new-env (:value name-node) nil))
        [:continue (update-frame stack {:stmt-index (unchecked-inc (long stmt-index)) :env new-env})])
      ;; Has values - evaluate expression list first, then bind in new scope
      (let [updated-block (update-frame stack {:state :eval-local
                                               :local-names (mapv :value name-nodes)
                                               :local-attribs (mapv :attrib name-nodes)})
            expr-frame (make-eval-exp-frame values-exp env)]
        [:continue (push-frame updated-block expr-frame)]))))

(defmethod handle-eval-exp [:block :eval-global-decl] [stack frame]
  (let [names (:global-names frame)
        values (:result frame)
        env (:env frame)
        values-vec (if (vector? values) values [values])
        name-value-pairs (map vector names (concat values-vec (repeat nil)))
        has-local-scopes? (seq (:scopes env))]
    (doseq [[name value] name-value-pairs]
      ;; If inside local scopes, place a marker so future assignments in this scope
      ;; bypass outer locals and go to the global env.  At top level (no local scopes)
      ;; the name is already global, so no marker is needed.
      (when has-local-scopes?
        (env/define! env name env/global-ref-marker))
      ;; assign! with marker redirects to global; without marker (top level) also goes global.
      (env/assign! env name value))
    (let [stmt-index (:stmt-index frame)]
      [:continue (update-frame stack {:state :executing
                                      :stmt-index (unchecked-inc (long stmt-index))
                                      :global-names nil
                                      :result nil})])))

(defmethod handle-eval-exp [:block :eval-local] [stack frame]
  ;; Local values evaluated, bind them in a fresh scope for upvalue isolation
  (let [names (:local-names frame)
        attribs (:local-attribs frame)
        values (:result frame)
        env (:env frame)
        values-vec (if (vector? values) values [values])
        new-env (env/push-scope env)
        name-value-attrib (map vector names (concat values-vec (repeat nil)) (or attribs (repeat nil)))]
    (doseq [[name value attrib] name-value-attrib]
      (env/define! new-env name value)
      ;; Validate to-be-closed values at binding time
      (when (= :close attrib)
        (when-not (or (nil? value) (= false value) (tables/get-metamethod value "__close"))
          (throw (ex-info (str "variable '" name "' got a non-closable value")
                          {:type :error})))))
    ;; Build updated close-list: prepend [value stmt-index name] entries for non-nil/false <close> values (LIFO)
    (let [cur-stmt-index (:stmt-index frame)
          new-close-list (reduce (fn [cl [name value attrib]]
                                   (if (and (= :close attrib)
                                            (not (nil? value))
                                            (not (= false value)))
                                     (cons [value cur-stmt-index name] cl)
                                     cl))
                                 (:close-list frame [])
                                 name-value-attrib)]
      [:continue (update-frame stack {:state :executing
                                      :stmt-index (unchecked-inc (long (:stmt-index frame)))
                                      :local-names nil
                                      :local-attribs nil
                                      :result nil
                                      :env new-env
                                      :close-list new-close-list})])))



(defmethod handle-eval-exp [:block :eval-assign-vars] [stack frame]
  ;; RHS of assignment evaluated - assign to each LHS var.
  ;; Per Lua semantics, ALL LHS table objects and keys must be evaluated
  ;; BEFORE any assignment happens (e.g. `i, a[i], a = 2, 1, 1` must use
  ;; the original `i` as the key for `a[i]`, not the new `i`).
  (let [vars (:assign-vars frame)
        raw-values (:result frame)
        env (:env frame)
        num-vars (count vars)
        values-vec (cond
                     (vector? raw-values) raw-values
                     (nil? raw-values) []
                     :else [raw-values])
        ;; Spread multi-value last element
        spread (if (empty? values-vec)
                 (repeat num-vars nil)
                 (let [last-val (last values-vec)
                       init-vals (butlast values-vec)]
                   (if (and (sequential? last-val) (not (string? last-val)))
                     (concat init-vals last-val (repeat nil))
                     (concat values-vec (repeat nil)))))
        ;; Pre-evaluate all LHS table objects and keys before any assignment
        pre-evals (mapv (fn [var-node]
                          (case (:type var-node)
                            :name nil
                            :index-access
                            (let [table-result (expr/eval-exp (:object var-node) env)
                                  tbl (if (and (vector? table-result)
                                               (types/is-multi-value-expr? (:object var-node)))
                                        (first table-result)
                                        table-result)
                                  key (types/unwrap-single (expr/eval-exp (:index var-node) env))]
                              {:tbl tbl :key key})
                            :field-access
                            (let [table-result (expr/eval-exp (:object var-node) env)
                                  tbl (if (and (vector? table-result)
                                               (types/is-multi-value-expr? (:object var-node)))
                                        (first table-result)
                                        table-result)]
                              {:tbl tbl :key (:value (:field var-node))})))
                        vars)]
    (doseq [[var-node val pre] (map vector vars spread pre-evals)]
      (case (:type var-node)
        :name
        (env/assign! env (:value var-node) val)
        :index-access
        (let [{:keys [tbl key]} pre]
          (try
            (tables/table-set-with-meta! tbl key val env)
            (catch ExceptionInfo e
              (if (= :error (:type (ex-data e)))
                (let [ctx (expr/operand-context-desc (:object var-node) env)]
                  (throw (ex-info (str (ex-message e) (or ctx "")) (ex-data e))))
                (throw e)))))
        :field-access
        (let [{:keys [tbl key]} pre]
          (try
            (tables/table-set-with-meta! tbl key val env)
            (catch ExceptionInfo e
              (if (= :error (:type (ex-data e)))
                (let [ctx (expr/operand-context-desc (:object var-node) env)]
                  (throw (ex-info (str (ex-message e) (or ctx "")) (ex-data e))))
                (throw e)))))))
    [:continue (update-frame stack {:state :executing
                                    :stmt-index (unchecked-inc (long (:stmt-index frame)))
                                    :assign-vars nil
                                    :result nil})]))

(defmethod handle-eval-exp [:block :await-substmt] [stack frame]
  ;; A sub-block (if-body, do-body, loop body, etc.) has completed.
  ;; Check if the result is a control-flow signal or normal completion.
  (let [result (:result frame)
        is-function-body (:function-body? frame)
        stmt-index (:stmt-index frame)
        env (:env frame)]
    (cond
      ;; Return signal from sub-block - run close-list then propagate.
      ;; If the block has to-be-closed variables, use the yieldable close-list runner
      ;; instead of the synchronous close-block-normal! (which blocks coroutine yields).
      (return-signal? result)
      (let [close-list (:close-list frame)
            ran? (:close-list-ran? frame)
            return-value (:values result)]
        (if (seq close-list)
          ;; Has close items — push async runner, handle completion in :closing
          (do
            (when ran? (reset! ran? true))
            (let [runner (make-close-list-runner-frame close-list env nil)
                  updated-block (update-frame stack {:state :closing
                                                     :pending {:type :return
                                                               :return-value return-value}})]
              [:continue (push-frame updated-block runner)]))
          ;; No close items — original synchronous path (close-block-normal! is a no-op)
          (let [_ (close-block-normal! frame env)
                [new-stack _] (pop-frame stack)]
            (cond
              (empty? new-stack)
              (do
                (pop-call-stack-if-needed! frame)
                [:done {:value return-value}])
              is-function-body
              (do
                (pop-call-stack-if-needed! frame)
                [:continue (set-frame-result new-stack return-value)])
              :else
              [:continue (set-frame-result new-stack result)]))))

      ;; Break signal - run close-list then propagate up (loop frames catch this)
      (break-signal? result)
      (let [_ (close-block-normal! frame env)
            [new-stack _] (pop-frame stack)]
        (if (empty? new-stack)
          [:done {:value nil}]
          [:continue (set-frame-result new-stack result)]))

      ;; Goto signal - check if label is in this block, jump or propagate
      (goto-signal? result)
      (let [label-name (:label result)
            label-map (:label-map frame)]
        (if-let [target-idx (get label-map label-name)]
          ;; Label found in this block - jump to it
          [:continue (update-frame stack {:state :executing
                                          :stmt-index target-idx
                                          :result nil})]
          ;; Not in this block - run close-list and propagate up
          (let [_ (close-block-normal! frame env)
                [new-stack _] (pop-frame stack)]
            (if (empty? new-stack)
              [:done {:value nil}]
              [:continue (set-frame-result new-stack result)]))))

      ;; Normal completion - fire pending end-line (if/while/for) then continue
      :else
      (let [end-line (:pending-end-line frame)
            _ (when end-line (fire-line! env end-line))]
        [:continue (update-frame stack {:state :executing
                                        :stmt-index (unchecked-inc (long stmt-index))
                                        :pending-end-line nil
                                        :result nil})]))))

(defmethod handle-eval-exp [:block :eval-if-cond] [stack frame]
  ;; If condition evaluated - choose which branch to execute
  (let [cond-val (:result frame)
        if-stmt (:if-stmt frame)
        env (:env frame)]
    (cond
      ;; Condition is truthy - execute then-block
      (types/lua-truthy? cond-val)
      (let [then-block (:then if-stmt)
            sub-statements (:statements then-block)
            sub-env (env/push-scope env)
            sub-block (make-block-frame sub-statements sub-env)
            updated-frame (update-frame stack {:state :await-substmt
                                               :if-stmt nil
                                               :result nil})]
        [:continue (push-frame updated-frame sub-block)])

      ;; Has elseif branches to try
      (seq (:elseifs if-stmt))
      (let [first-elseif (first (:elseifs if-stmt))
            rest-elseifs (vec (rest (:elseifs if-stmt)))
            ;; Build reduced if-stmt representing remaining elseif/else checks
            reduced-if {:type :if
                        :condition (:condition first-elseif)
                        :then (:body first-elseif)
                        :elseifs rest-elseifs
                        :else (:else if-stmt)}
            updated-frame (update-frame stack {:state :eval-if-cond
                                               :if-stmt reduced-if
                                               :result nil})
            cond-frame (make-eval-exp-frame (:condition first-elseif) env)]
        [:continue (push-frame updated-frame cond-frame)])

      ;; Has else branch
      (:else if-stmt)
      (let [else-block (-> if-stmt :else :body)
            sub-statements (:statements else-block)
            sub-env (env/push-scope env)
            sub-block (make-block-frame sub-statements sub-env)
            updated-frame (update-frame stack {:state :await-substmt
                                               :if-stmt nil
                                               :result nil})]
        [:continue (push-frame updated-frame sub-block)])

      ;; No matching branch - fire end-line, skip if, continue to next statement
      :else
      (let [end-line (:pending-end-line frame)
            _ (when end-line (fire-line! env end-line))]
        [:continue (update-frame stack {:state :executing
                                        :stmt-index (unchecked-inc (long (:stmt-index frame)))
                                        :if-stmt nil
                                        :pending-end-line nil
                                        :result nil})]))))



;;; While Loop Frame
;; Frame type: :while-loop
;; States: :start -> :eval-cond -> :exec-body -> (back to :eval-cond) -> done

(defn make-while-frame [stmt env]
  (make-frame :while-loop :start nil env :stmt stmt))

(defmethod handle-eval-exp [:while-loop :start] [stack frame]
  ;; Start: fire condition line hook, count a step, evaluate condition
  (let [stmt (:stmt frame)
        cond-node (:condition stmt)
        env (:env frame)
        cond-line (or (:line cond-node) (:op-line cond-node) (:line stmt))
        _ (when cond-line (fire-line! env cond-line))
        _ (env/increment-steps! env)
        updated-frame (update-frame stack {:state :eval-cond})
        cond-frame (make-eval-exp-frame cond-node env)]
    [:continue (push-frame updated-frame cond-frame)]))

(defmethod handle-eval-exp [:while-loop :eval-cond] [stack frame]
  ;; Condition evaluated - check it
  (let [cond-val (:result frame)
        stmt (:stmt frame)
        env (:env frame)]
    (if (types/lua-truthy? cond-val)
      ;; True - execute body in new scope
      (let [body-statements (-> stmt :body :statements)
            loop-env (env/push-scope env)
            body-block (make-block-frame body-statements loop-env)
            updated-frame (update-frame stack {:state :exec-body :result nil})]
        [:continue (push-frame updated-frame body-block)])
      ;; False - fire end-line then exit loop
      (let [_ (fire-line! env (:end-line stmt))
            [new-stack _] (pop-frame stack)]
        (if (empty? new-stack)
          [:done {:value nil}]
          [:continue (set-frame-result new-stack nil)])))))

(defmethod handle-eval-exp [:while-loop :exec-body] [stack frame]
  ;; Body executed - handle control flow or re-check condition
  (let [result (:result frame)
        stmt (:stmt frame)
        env (:env frame)]
    (cond
      ;; Break - exit loop normally
      (break-signal? result)
      (let [[new-stack _] (pop-frame stack)]
        (if (empty? new-stack)
          [:done {:value nil}]
          [:continue (set-frame-result new-stack nil)]))

      ;; Return - propagate up
      (return-signal? result)
      (let [[new-stack _] (pop-frame stack)]
        (if (empty? new-stack)
          [:done {:value (:values result)}]
          [:continue (set-frame-result new-stack result)]))

      ;; Goto - propagate up (loops don't catch goto)
      (goto-signal? result)
      (let [[new-stack _] (pop-frame stack)]
        (if (empty? new-stack)
          [:done {:value nil}]
          [:continue (set-frame-result new-stack result)]))

      ;; Normal - fire condition line, count a step, re-evaluate condition
      :else
      (let [cond-node (-> stmt :condition)
            cond-line (or (:line cond-node) (:op-line cond-node) (:line stmt))
            _ (fire-line! env cond-line)
            _ (env/increment-steps! env)
            updated-frame (update-frame stack {:state :eval-cond :result nil})
            cond-frame (make-eval-exp-frame cond-node env)]
        [:continue (push-frame updated-frame cond-frame)]))))

;;; For-Numeric Loop Frame
;; Frame type: :for-numeric-loop
;; States: :start -> :got-start -> :got-end -> :got-step -> :check -> :exec-body -> ...

(defn- coerce-for-number
  "Coerce a value to a number for use in numeric for loop.
   Strings are converted to numbers (Lua 5.3 semantics).
   Throws if the value cannot be converted."
  [v label]
  (cond
    (number? v) v
    (string? v) (let [trimmed (str/trim v)
                      n (try (read-string trimmed)
                             (catch Exception _ nil))]
                  (if (number? n) n
                                  (throw (ex-info (str "'for' " label " value must be a number")
                                                  {:type :error}))))
    :else (throw (ex-info (str "'for' " label " value must be a number (a "
                               (tables/lua-type-name v) " value)")
                          {:type :error}))))


(defn make-for-numeric-frame [stmt env]
  (make-frame :for-numeric-loop :start nil env :stmt stmt))

(defmethod handle-eval-exp [:for-numeric-loop :start] [stack frame]
  (let [start-node (-> frame :stmt :start)
        env (:env frame)
        updated-frame (update-frame stack {:state :got-start})
        start-frame (make-eval-exp-frame start-node env)]
    [:continue (push-frame updated-frame start-frame)]))

(defmethod handle-eval-exp [:for-numeric-loop :got-start] [stack frame]
  (let [start-val (coerce-for-number (types/unwrap-single (:result frame)) "initial")
        end-node (-> frame :stmt :end)
        env (:env frame)
        updated-frame (update-frame stack {:state :got-end
                                           :loop-start start-val
                                           :result nil})
        end-frame (make-eval-exp-frame end-node env)]
    [:continue (push-frame updated-frame end-frame)]))

(defmethod handle-eval-exp [:for-numeric-loop :got-end] [stack frame]
  (let [end-val (coerce-for-number (types/unwrap-single (:result frame)) "limit")
        step-node (-> frame :stmt :step)
        env (:env frame)]
    (if step-node
      ;; Has explicit step - evaluate it
      (let [updated-frame (update-frame stack {:state :got-step
                                               :loop-end end-val
                                               :result nil})
            step-frame (make-eval-exp-frame step-node env)]
        [:continue (push-frame updated-frame step-frame)])
      ;; No step - integer loop if start is integer, else float loop
      ;; Integer loop: keep start/end as-is (compare as doubles in :check); step=1
      ;; Float loop: coerce all to double
      (let [start (:loop-start frame)
            [start end step] (if (integer? start)
                               [start end-val 1]
                               [(double start) (double end-val) 1.0])]
        [:continue (update-frame stack {:state :check
                                        :loop-start start
                                        :loop-end end
                                        :loop-step step
                                        :loop-current start
                                        :result nil})]))))

(defmethod handle-eval-exp [:for-numeric-loop :got-step] [stack frame]
  (let [step-val (coerce-for-number (types/unwrap-single (:result frame)) "step")
        _ (when (== (double step-val) 0.0)
            (throw (ex-info "'for' step is zero" {:type :error})))
        start (:loop-start frame)
        end (:loop-end frame)
        ;; Lua 5.3 loop type: integer if init AND step are integers (limit gets floor/ceil'd);
        ;; float otherwise (any of init/step is float → coerce all to double).
        [start end step] (if (and (integer? start) (integer? step-val))
                           ;; Integer loop: keep start/end as-is (compare as doubles in :check)
                           [start end step-val]
                           ;; Float loop: coerce all to double
                           [(double start) (double end) (double step-val)])]
    [:continue (update-frame stack {:state :check
                                    :loop-start start
                                    :loop-end end
                                    :loop-step step
                                    :loop-current start
                                    :result nil})]))

(defmethod handle-eval-exp [:for-numeric-loop :check] [stack frame]
  (let [current (:loop-current frame)
        end (:loop-end frame)
        step (:loop-step frame)
        stmt (:stmt frame)
        env (:env frame)
        for-line (:line stmt)
        end-line (:end-line stmt)
        ;; Check loop condition: integer comparison for integer limits, double for float limits
        ;; (Using double for large integers like LLONG_MAX ± 10 would lose precision)
        should-continue (if (and (integer? current) (integer? end))
                          (if (>= (long step) 0) (<= (long current) (long end)) (>= (long current) (long end)))
                          (if (>= (double step) 0.0)
                            (<= (double current) (double end))
                            (>= (double current) (double end))))]
    (if should-continue
      ;; Force-fire for-line on each continue (PUC-Lua FORLOOP fires on every iteration)
      (let [_ (force-fire-line! env for-line)
            _ (fire-hook! env "count" nil)
            _ (env/increment-steps! env)
            var-name (-> stmt :var :value)
            loop-env (env/push-scope env)
            _ (env/define! loop-env var-name current)
            body-statements (-> stmt :body :statements)
            body-block (make-block-frame body-statements loop-env)
            updated-frame (update-frame stack {:state :exec-body :result nil})]
        [:continue (push-frame updated-frame body-block)])
      ;; Exit: if end-line differs from for-line, force-fire for-line first (PUC-Lua FORLOOP
      ;; exit check), then fire end-line. If same line, just fire end-line (deduped by lastline).
      (let [_ (if (and end-line for-line (not= end-line for-line))
                 (do (force-fire-line! env for-line)
                     (fire-line! env end-line))
                 (fire-line! env end-line))
            _ (fire-hook! env "count" nil)
            [new-stack _] (pop-frame stack)]
        (if (empty? new-stack)
          [:done {:value nil}]
          [:continue (set-frame-result new-stack nil)])))))

(defmethod handle-eval-exp [:for-numeric-loop :exec-body] [stack frame]
  (let [result (:result frame)
        step (:loop-step frame)]
    (cond
      (break-signal? result)
      (let [[new-stack _] (pop-frame stack)]
        (if (empty? new-stack)
          [:done {:value nil}]
          [:continue (set-frame-result new-stack nil)]))

      (return-signal? result)
      (let [[new-stack _] (pop-frame stack)]
        (if (empty? new-stack)
          [:done {:value (:values result)}]
          [:continue (set-frame-result new-stack result)]))

      (goto-signal? result)
      (let [[new-stack _] (pop-frame stack)]
        (if (empty? new-stack)
          [:done {:value nil}]
          [:continue (set-frame-result new-stack result)]))

      ;; Normal - increment and check again
      :else
      (let [current (:loop-current frame)
            int-loop? (integer? current)]
        (if int-loop?
          ;; Integer loop: detect overflow before advancing.
          ;; If step > 0 and next < current, or step < 0 and next > current,
          ;; adding step overflowed — the loop is exhausted.
          (let [next-current (unchecked-add (long current) (long step))
                overflowed? (if (pos? (long step))
                              (< next-current (long current))
                              (> next-current (long current)))]
            (if overflowed?
              (let [[new-stack _] (pop-frame stack)]
                (if (empty? new-stack)
                  [:done {:value nil}]
                  [:continue (set-frame-result new-stack nil)]))
              [:continue (update-frame stack {:state :check
                                              :loop-current next-current
                                              :result nil})]))
          ;; Float loop: no overflow detection needed
          [:continue (update-frame stack {:state :check
                                          :loop-current (+ (double current) (double step))
                                          :result nil})])))))

;;; For-Generic Loop Frame
;; Frame type: :for-generic-loop
;; States: :start -> :got-exprs -> :call-iter -> :got-iter-result -> :exec-body -> ...

(defn- find-parent-env-atom
  "Scan execution stack top-to-bottom for the nearest :block frame with a :frame-env-atom.
  Used to thread the enclosing function's env-atom into for-generic body blocks so that
  debug.getlocal sees the for-loop's (for state) scopes."
  [stack]
  (loop [s stack]
    (when-not (empty? s)
      (let [f (peek s)]
        (if (and (= :block (:type f)) (:frame-env-atom f))
          (:frame-env-atom f)
          (recur (pop s)))))))

(defn make-for-generic-frame [stmt env]
  (make-frame :for-generic-loop :start nil env :stmt stmt))

(defmethod handle-eval-exp [:for-generic-loop :start] [stack frame]
  ;; Evaluate the expression list to get [iter-fn, state, initial]
  (let [exprs-node (-> frame :stmt :expressions)
        env (:env frame)
        updated-frame (update-frame stack {:state :got-exprs})
        exprs-frame (make-eval-exp-frame exprs-node env)]
    [:continue (push-frame updated-frame exprs-frame)]))

(defn- run-for-generic-close!
  "Run __close on the for-generic loop's closing value (4th iterator value).
  Throws if the __close metamethod raises an error."
  [frame env]
  (let [close-val (:close-val frame)]
    (when (and close-val (not (false? close-val)))
      (when-let [err (run-close-list! [close-val] env nil)]
        (throw err)))))

(defmethod handle-eval-exp [:for-generic-loop :got-exprs] [stack frame]
  ;; Extract iter-fn, state, initial, and optional close-val (4th value) from expressions.
  ;; The 4th value is a to-be-closed variable per Lua 5.4+ spec.
  ;; Push (for state) scopes into the env for Lua 5.5 debug.getlocal visibility:
  ;;   scope1: (for state) = iter-fn
  ;;   scope2: (for state) = state
  ;;   scope3: (for state) = close-val  (only when close-val is present)
  ;; The parent env-atom (enclosing function's live-env tracker) is stored so
  ;; the for-body block can update it each iteration, keeping debug.getlocal current.
  (let [exprs (:result frame)
        exprs-vec (cond
                    (vector? exprs) exprs
                    (nil? exprs) []
                    :else [exprs])
        iter-fn (nth exprs-vec 0 nil)
        state (nth exprs-vec 1 nil)
        initial (nth exprs-vec 2 nil)
        close-val (nth exprs-vec 3 nil)
        env (:env frame)
        _ (when (and close-val (not (false? close-val))
                     (nil? (tables/get-metamethod close-val "__close")))
            (throw (ex-info "value has no __close metamethod"
                            {:type :error :line (some-> env :current-line deref)})))
        ;; Push (for state) scopes: one each for iter-fn and state, plus close-val if present
        for-env1 (env/push-scope env)
        _ (env/define! for-env1 "(for state)" iter-fn)
        for-env2 (env/push-scope for-env1)
        _ (env/define! for-env2 "(for state)" state)
        for-env (if (and close-val (not (false? close-val)))
                  (let [e3 (env/push-scope for-env2)]
                    (env/define! e3 "(for state)" close-val)
                    e3)
                  for-env2)
        ;; Find the enclosing function's frame-env-atom for debug.getlocal support
        parent-ea (find-parent-env-atom (pop stack))]
    [:continue (update-frame stack {:state :call-iter
                                    :iter-fn iter-fn
                                    :iter-state state
                                    :iter-control initial
                                    :close-val close-val
                                    :env for-env
                                    :parent-ea parent-ea
                                    :result nil})]))

(defmethod handle-eval-exp [:for-generic-loop :call-iter] [stack frame]
  ;; Count a step per iteration and call iterator function(state, control).
  ;; Push a "for iterator" call-stack frame so debug.getinfo(1) inside the
  ;; iterator function reports name="for iterator", namewhat="for iterator".
  ;; The :call-stack atom is shared between env and the iterator's func-env
  ;; (both derive from the same root via push-scope), so the frame is visible
  ;; from inside the iterator.
  (let [iter-fn (:iter-fn frame)
        iter-state (:iter-state frame)
        iter-control (:iter-control frame)
        env (:env frame)
        _ (env/increment-steps! env)
        _ (env/push-stack-frame! env "for iterator" nil nil iter-fn nil 0 "for iterator")
        result (try
                 (call-function-from-stack iter-fn [iter-state iter-control] env)
                 (finally
                   (env/pop-stack-frame! env)))]
    [:continue (update-frame stack {:state :got-iter-result
                                    :result result})]))

(defmethod handle-eval-exp [:for-generic-loop :got-iter-result] [stack frame]
  ;; Got iteration result - check if done (first value nil = exhausted)
  (let [result (:result frame)
        result-vec (cond
                     (vector? result) result
                     (nil? result) []
                     :else [result])
        first-val (first result-vec)
        stmt (:stmt frame)
        env (:env frame)
        for-line (:line stmt)
        end-line (:end-line stmt)]
    (if (nil? first-val)
      ;; Iterator exhausted - fire for-line/end-line hooks, run __close on the 4th value if any
      (let [_ (if (and end-line for-line (not= end-line for-line))
                 (do (force-fire-line! env for-line)
                     (fire-line! env end-line))
                 (fire-line! env end-line))
            _ (run-for-generic-close! frame env)
            [new-stack _] (pop-frame stack)]
        (if (empty? new-stack)
          [:done {:value nil}]
          [:continue (set-frame-result new-stack nil)]))
      ;; Execute body - force-fire for-line (PUC-Lua TFORLOOP fires on each continue)
      (let [_ (force-fire-line! env for-line)
            name-nodes (-> stmt :names :names)
            loop-env (env/push-scope env)
            _ (doseq [[name-node val] (map vector name-nodes
                                           (concat result-vec (repeat nil)))]
                (env/define! loop-env (:value name-node) val))
            body-statements (-> stmt :body :statements)
            ;; Give body-block the enclosing function's env-atom so debug.getlocal
            ;; sees (for state) scopes and loop vars at the function's call-stack level.
            parent-ea (:parent-ea frame)
            body-block (cond-> (make-block-frame body-statements loop-env)
                         parent-ea (assoc :frame-env-atom parent-ea))
            ;; Save first value as new control variable for next iteration
            updated-frame (update-frame stack {:state :exec-body
                                               :iter-control first-val
                                               :result nil})]
        [:continue (push-frame updated-frame body-block)]))))

(defmethod handle-eval-exp [:for-generic-loop :exec-body] [stack frame]
  (let [result (:result frame)
        env (:env frame)]
    (cond
      (break-signal? result)
      (let [_ (run-for-generic-close! frame env)
            [new-stack _] (pop-frame stack)]
        (if (empty? new-stack)
          [:done {:value nil}]
          [:continue (set-frame-result new-stack nil)]))

      (return-signal? result)
      (let [_ (run-for-generic-close! frame env)
            [new-stack _] (pop-frame stack)]
        (if (empty? new-stack)
          [:done {:value (:values result)}]
          [:continue (set-frame-result new-stack result)]))

      (goto-signal? result)
      (let [_ (run-for-generic-close! frame env)
            [new-stack _] (pop-frame stack)]
        (if (empty? new-stack)
          [:done {:value nil}]
          [:continue (set-frame-result new-stack result)]))

      ;; Normal - call iterator again
      :else
      [:continue (update-frame stack {:state :call-iter :result nil})])))

;;; Repeat-Until Loop Frame
;; Frame type: :repeat-loop
;; States: :start -> :exec-body -> :eval-cond -> (back to :exec-body or done)

(defn make-repeat-frame [stmt env]
  (make-frame :repeat-loop :start nil env :stmt stmt))

(defmethod handle-eval-exp [:repeat-loop :start] [stack frame]
  ;; Count a step and execute body first (always runs at least once)
  (let [stmt (:stmt frame)
        env (:env frame)
        _ (env/increment-steps! env)
        loop-env (env/push-scope env)
        body-statements (-> stmt :body :statements)
        body-block (make-block-frame body-statements loop-env)
        ;; Save loop-env so condition can see body's locals
        updated-frame (update-frame stack {:state :exec-body
                                           :body-env loop-env})]
    [:continue (push-frame updated-frame body-block)]))

(defmethod handle-eval-exp [:repeat-loop :exec-body] [stack frame]
  ;; Body executed - handle signals or evaluate condition in body scope
  (let [result (:result frame)
        stmt (:stmt frame)
        body-env (:body-env frame)]
    (cond
      (break-signal? result)
      (let [[new-stack _] (pop-frame stack)]
        (if (empty? new-stack)
          [:done {:value nil}]
          [:continue (set-frame-result new-stack nil)]))

      (return-signal? result)
      (let [[new-stack _] (pop-frame stack)]
        (if (empty? new-stack)
          [:done {:value (:values result)}]
          [:continue (set-frame-result new-stack result)]))

      (goto-signal? result)
      (let [[new-stack _] (pop-frame stack)]
        (if (empty? new-stack)
          [:done {:value nil}]
          [:continue (set-frame-result new-stack result)]))

      ;; Normal - fire condition line hook, evaluate condition in body-env (locals visible)
      :else
      (let [cond-node (:condition stmt)
            cond-line (or (:line cond-node) (:op-line cond-node) (:line stmt))
            _ (when cond-line (fire-line! body-env cond-line))
            updated-frame (update-frame stack {:state :eval-cond :result nil})
            cond-frame (make-eval-exp-frame cond-node body-env)]
        [:continue (push-frame updated-frame cond-frame)]))))

(defmethod handle-eval-exp [:repeat-loop :eval-cond] [stack frame]
  ;; Condition evaluated - true means stop (repeat until cond)
  (let [cond-val (:result frame)
        stmt (:stmt frame)
        env (:env frame)]
    (if (types/lua-truthy? cond-val)
      ;; Condition true = stop looping
      (let [[new-stack _] (pop-frame stack)]
        (if (empty? new-stack)
          [:done {:value nil}]
          [:continue (set-frame-result new-stack nil)]))
      ;; Condition false = count a step and loop again with fresh scope
      (let [_ (env/increment-steps! env)
            loop-env (env/push-scope env)
            body-statements (-> stmt :body :statements)
            body-block (make-block-frame body-statements loop-env)
            updated-frame (update-frame stack {:state :exec-body
                                               :body-env loop-env
                                               :result nil})]
        [:continue (push-frame updated-frame body-block)]))))

;;; pcall-frame: runs pcall/xpcall body as explicit stack machine frames
;; This allows coroutine yields inside the body to propagate through the
;; frame stack with full state preservation, enabling proper resume semantics.
;;
;; Frame fields:
;;   :body-fn    - Lua or native function to call under pcall protection
;;   :body-args  - Arguments to pass to body-fn
;;   :outer-wrap - nil (plain pcall), :xpcall (f with handler), :xpcall-pcall (xpcall(pcall,...))
;;   :msgh       - Error handler (xpcall only)
;;   :env        - Environment at the call site
;;
;; States: :run-body -> :body-running -> (done, via set-frame-result from body block)

(defmethod handle-eval-exp [:pcall-frame :run-body] [stack frame]
  (let [body-fn (:body-fn frame)
        body-args (:body-args frame)
        env (:env frame)]
    (cond
      ;; Lua function body: push body block frame above pcall-frame so yields
      ;; propagate through the full stack and state is preserved across resumes.
      ;; Also push a call-stack frame for the body function so debug.getlocal
      ;; level counting and frame-env-atom tracking work inside the pcall body.
      (= :lua-function (:type body-fn))
      (let [body-joins (env/get-upvalue-joins body-fn)
            outer-scope-count (count (:scopes (:env body-fn)))
            base-body-env (-> (env/push-scope (:env body-fn))
                              (assoc :outer-scope-count outer-scope-count))
            func-env (if body-joins (assoc base-body-env :upvalue-joins body-joins) base-body-env)
            params (:params body-fn)
            has-varargs (:varargs body-fn)
            vararg-name (:vararg-name body-fn)
            num-params (count params)
            _ (doseq [[param-name arg-val] (map vector params (concat body-args (repeat nil)))]
                (env/define! func-env param-name arg-val))
            _ (when has-varargs
                (let [varargs (vec (drop num-params body-args))]
                  (if vararg-name
                    (let [vt (tables/make-table)]
                      (tables/table-set! vt "n" (count varargs))
                      (dorun (map-indexed (fn [i v] (tables/table-set! vt (unchecked-inc (long i)) v)) varargs))
                      (env/define! func-env vararg-name vt)
                      (env/define! func-env "..." {:vararg-table vt}))
                    (env/define! func-env "..." varargs))))
            stmts (:statements (:body body-fn))
            fn-name (or (:name body-fn) "?")
            env-atom (atom func-env)
            _ (env/push-stack-frame! func-env fn-name 0 0 body-fn env-atom)
            body-block (assoc (make-function-block-frame stmts func-env)
                         :call-fn-env func-env
                         :frame-env-atom env-atom)
            updated-frame (update-frame stack {:state :body-running})]
        [:continue (push-frame updated-frame body-block)])

      ;; Native function body: call synchronously.
      ;; If the native fn yields (e.g. xpcall(coroutine.yield, handler)), propagate the
      ;; yield by transitioning to :awaiting-native-yield so the coroutine can be resumed.
      ;; Other yields (e.g. table.sort + yield comparator) also propagate here.
      (fn? body-fn)
      (let [outer-wrap (:outer-wrap frame)
            msgh (:msgh frame)]
        (try
          (let [r (call-native-with-arity-retry body-fn body-args)
                _ (when-let [e (:pcall-call-env frame)] (env/pop-stack-frame! e))
                [new-stack _] (pop-frame stack)
                result (vec (cons true (flatten [r])))]
            (if (empty? new-stack)
              [:done {:value result}]
              [:continue (set-frame-result new-stack result)]))
          (catch ExceptionInfo e
            (cond
              (= :coro-yield (:type (ex-data e)))
              ;; Yield from native body: save frame, propagate yield to coroutine runner.
              ;; On resume, :awaiting-native-yield handler re-calls body-fn to get resume values.
              [:yield {:values (:values (ex-data e))
                       :stack (update-frame stack {:state :awaiting-native-yield})}]
              (#{:self-close :exit} (:type (ex-data e)))
              ;; self-close and os.exit must not be caught by pcall; re-throw to propagate up.
              (throw e)
              :else
              (let [_ (when-let [ce (:pcall-call-env frame)] (env/pop-stack-frame! ce))
                    [new-stack _] (pop-frame stack)
                    result (apply-native-pcall-error outer-wrap msgh env e)]
                (if (empty? new-stack)
                  [:done {:value result}]
                  [:continue (set-frame-result new-stack result)]))))
          (catch StackOverflowError _
            (let [_ (when-let [e (:pcall-call-env frame)] (env/pop-stack-frame! e))
                  [new-stack _] (pop-frame stack)
                  result (apply-native-pcall-error outer-wrap msgh env
                                                   (ex-info "C stack overflow" {:type :error}))]
              (if (empty? new-stack)
                [:done {:value result}]
                [:continue (set-frame-result new-stack result)])))))

      ;; Other callable (table with __call, etc.): use call-function-from-stack.
      :else
      (let [_ (when-let [e (:pcall-call-env frame)] (env/pop-stack-frame! e))
            [new-stack _] (pop-frame stack)
            outer-wrap (:outer-wrap frame)
            msgh (:msgh frame)
            result (try
                     (let [r (call-function-from-stack body-fn body-args env)]
                       (vec (cons true (flatten [r]))))
                     (catch ExceptionInfo e
                       (cond
                         (#{:self-close :exit} (:type (ex-data e))) (throw e)
                         (= :coro-yield (:type (ex-data e)))
                         (apply-native-pcall-error outer-wrap msgh env
                                                   (ex-info "attempt to yield across a C-call boundary"
                                                            {:type :error}))
                         :else (apply-native-pcall-error outer-wrap msgh env e)))
                     (catch StackOverflowError _
                       (apply-native-pcall-error outer-wrap msgh env
                                                 (ex-info "C stack overflow" {:type :error}))))]
        (if (empty? new-stack)
          [:done {:value result}]
          [:continue (set-frame-result new-stack result)])))))

(defmethod handle-eval-exp [:pcall-frame :body-running] [stack frame]
  ;; Body Lua function completed normally. Wrap result in pcall/xpcall success form.
  (let [body-result (:result frame)
        outer-wrap (:outer-wrap frame)
        _ (when-let [e (:pcall-call-env frame)] (env/pop-stack-frame! e))
        [new-stack _] (pop-frame stack)
        wrapped (case outer-wrap
                  ;; xpcall(pcall, handler, real-body): success = [true, true, body-result...]
                  :xpcall-pcall (into [true true] (flatten [body-result]))
                  ;; plain pcall or xpcall(lua-fn, ...) success: [true, body-result...]
                  (vec (cons true (flatten [body-result]))))]
    (if (empty? new-stack)
      [:done {:value wrapped}]
      [:continue (set-frame-result new-stack wrapped)])))

(defmethod handle-eval-exp [:pcall-frame :awaiting-native-yield] [stack frame]
  ;; Native body function yielded; the coroutine has been resumed.
  ;; Re-call the body function: coroutine.yield (and similar) check :resume-values-set
  ;; and return the resume values instead of yielding again.
  (let [body-fn (:body-fn frame)
        body-args (:body-args frame)
        outer-wrap (:outer-wrap frame)
        msgh (:msgh frame)
        env (:env frame)]
    (try
      (let [r (call-native-with-arity-retry body-fn body-args)
            _ (when-let [e (:pcall-call-env frame)] (env/pop-stack-frame! e))
            [new-stack _] (pop-frame stack)
            result (vec (cons true (flatten [r])))]
        (if (empty? new-stack)
          [:done {:value result}]
          [:continue (set-frame-result new-stack result)]))
      (catch ExceptionInfo e
        (cond
          (= :coro-yield (:type (ex-data e)))
          ;; Yielded again (e.g. coroutine.yield called multiple times through xpcall)
          [:yield {:values (:values (ex-data e))
                   :stack (update-frame stack {:state :awaiting-native-yield})}]
          (#{:self-close :exit} (:type (ex-data e)))
          (throw e)
          :else
          (let [_ (when-let [ce (:pcall-call-env frame)] (env/pop-stack-frame! ce))
                [new-stack _] (pop-frame stack)
                result (apply-native-pcall-error outer-wrap msgh env e)]
            (if (empty? new-stack)
              [:done {:value result}]
              [:continue (set-frame-result new-stack result)]))))
      (catch StackOverflowError _
        (let [_ (when-let [e (:pcall-call-env frame)] (env/pop-stack-frame! e))
              [new-stack _] (pop-frame stack)
              result (apply-native-pcall-error outer-wrap msgh env
                                               (ex-info "C stack overflow" {:type :error}))]
          (if (empty? new-stack)
            [:done {:value result}]
            [:continue (set-frame-result new-stack result)]))))))

;; Default handler for unimplemented expression types
(defmethod handle-eval-exp :default [_stack frame]
  [:error (ex-info (str "Unimplemented expression type: "
                        [(:type (:node frame)) (:state frame)])
                   {:frame frame})])

;;; Stack Machine Runner

;;; pcall/xpcall stack machine frame support
;;
;; pcall and xpcall are tagged with :clua/pcall / :clua/xpcall metadata.
;; When the stack machine encounters a call to these functions, it converts
;; them into :pcall-frame frames instead of calling them as native functions.
;; This lets coroutine yields inside the body propagate through the full
;; stack-machine frame stack, preserving accumulated state across resumes.

(defn- lua-pcall?
  "Returns true if f is the pcall function (tagged with :clua/pcall metadata)."
  [f]
  (:clua/pcall (meta f)))

(defn- lua-xpcall?
  "Returns true if f is the xpcall function (tagged with :clua/xpcall metadata)."
  [f]
  (:clua/xpcall (meta f)))

(defn- format-source-name
  "Convert a Lua source name to a display string for error prefixes.
  '=name' -> 'name'; '@file' -> 'file'; 'text' -> '[string \"text\"]'"
  [s]
  (when s
    (cond
      (str/starts-with? s "=") (subs s 1)
      (str/starts-with? s "@") (subs s 1)
      :else
      (let [first-line (first (str/split-lines s))
            truncated (if (> (count first-line) 50)
                        (str (subs first-line 0 47) "...")
                        first-line)]
        (str "[string \"" truncated "\"]")))))

(defn extract-lua-error
  "Extract the Lua error value from a caught ExceptionInfo.
  Mirrors pcall-error-value from stdlib.clj without creating a circular dep.
  For runtime errors with :error-line/:error-source, prepends 'source:line: ' prefix."
  [e]
  (if-let [data (ex-data e)]
    (if (contains? data :lua-error)
      (let [lua-err (:lua-error data)]
        (cond
          (nil? lua-err) "<no error object>"
          (string? lua-err) (ex-message e)
          :else lua-err))
      ;; Runtime error without :lua-error: add location prefix if available
      (let [msg (ex-message e)
            line (:error-line data)
            source (:error-source data)
            formatted (format-source-name source)]
        (if (and line formatted)
          (str formatted ":" line ": " msg)
          msg)))
    (ex-message e)))

;;; Close-List Runner Frame
;;
;; Executes __close metamethods one at a time as stack machine sub-frames,
;; allowing coroutine.yield from within __close handlers.
;;
;; States: :scan -> :after-call -> :scan -> ... -> (empty items) -> done
;;
;; Error handling: errors from __close calls are routed back by recover-from-pcall
;; into the :after-call state via :call-error, so the runner absorbs them and
;; continues with remaining items (Lua 5.5 spec: close errors don't stop the list).

(defmethod handle-eval-exp [:close-list-runner :scan] [stack frame]
  (let [items (:items frame)
        current-err (:current-err frame)
        env (:env frame)]
    (if (empty? items)
      ;; All items processed - return current-err to parent frame (nil = success)
      (let [[new-stack _] (pop-frame stack)]
        (if (empty? new-stack)
          [:done {:value current-err}]
          [:continue (set-frame-result new-stack current-err)]))
      ;; Process next item: get __close metamethod and push a call frame for it
      (let [entry (first items)
            value (if (vector? entry) (first entry) entry)
            mm (tables/get-metamethod value "__close")]
        (if mm
          (let [err-arg (when current-err (extract-lua-error current-err))
                call-args (if err-arg [value err-arg] [value])
                ;; Advance items now so :after-call has the remaining list
                updated-runner (update-frame stack {:state :after-call
                                                    :items (vec (rest items))})
                ;; Push a function-call frame that handles Lua fns, native fns, and yields
                call-frame (assoc (make-eval-exp-frame close-call-node env)
                                  :state :call
                                  :target-val mm
                                  :arg-vals call-args)]
            [:continue (push-frame updated-runner call-frame)])
          ;; Missing __close metamethod (was removed after variable was bound)
          (let [missing-err (ex-info "missing metamethod 'close'"
                                     {:type :error :lua-error "missing metamethod 'close'"})
                new-err (or missing-err current-err)]
            [:continue (update-frame stack {:state :scan
                                            :items (vec (rest items))
                                            :current-err new-err})]))))))

(defmethod handle-eval-exp [:close-list-runner :after-call] [stack frame]
  ;; A __close call completed - either normally (:result set by the call frame) or
  ;; via error routed by recover-from-pcall (:call-error set). Return values are ignored.
  (let [call-error (:call-error frame)
        current-err (:current-err frame)
        new-err (when call-error
                  ;; Decorate string errors with "\nin metamethod 'close'"
                  (let [data (ex-data call-error)
                        lua-err (when (contains? data :lua-error) (:lua-error data))]
                    (if (or (nil? lua-err) (string? lua-err))
                      (let [close-msg (str (ex-message call-error) "\nin metamethod 'close'")]
                        (ex-info close-msg (assoc data :lua-error close-msg)))
                      call-error)))
        updated-err (or new-err current-err)]
    [:continue (update-frame stack {:state :scan
                                    :current-err updated-err
                                    :call-error nil})]))

(defmethod handle-eval-exp [:error-propagation :await-runner] [stack frame]
  ;; A close-list runner (pushed by recover-from-pcall for the async error path)
  ;; has completed. (:result frame) is the final error after running all __close
  ;; metamethods. Continue error recovery on the remaining stack below this frame.
  (let [final-err (:result frame)
        remaining (:remaining frame)
        self-close? (:self-close? frame)
        recovery (recover-frames-loop remaining final-err self-close?)]
    (cond
      (not (vector? recovery))
      [:done {:value (:value recovery)}]
      (= :continue (first recovery))
      [:continue (second recovery)]
      :else  ; [:propagate err]
      [:error (second recovery)])))

;;; To-Be-Closed Variables helpers
;;
;; run-close-list! and close-block-normal! implement __close metamethod
;; invocation for <close>-attributed local variables.

(defn run-close-list!
  "Run __close metamethods for close-list items (already in LIFO run-order).
  Items may be raw Lua values or [value stmt-index] vectors (from the block close-list).
  initial-err is the current error exception being propagated, or nil (normal exit).
  Returns nil on success, or the final error exception if any __close threw."
  [close-list env initial-err]
  (loop [items (seq close-list)
         current-err initial-err]
    (if (empty? items)
      current-err
      (let [entry (first items)
            value (if (vector? entry) (first entry) entry)
            mm (tables/get-metamethod value "__close")]
        (if mm
          (let [err-arg (when current-err (extract-lua-error current-err))
                ;; When there is no error, __close is called with just (value).
                ;; When there is an error, __close is called with (value, err).
                ;; select("#", ...) inside __close must count correctly.
                call-args (if err-arg [value err-arg] [value])
                ;; Push a call stack frame so debug.getinfo level-counting works correctly
                ;; inside __close (the enclosing function is visible at level 2).
                ;; Name "close" so debug.getinfo(2).name returns "close" in return hooks.
                _ (env/push-stack-frame! env "close" nil nil mm nil)
                new-err (try
                          ;; Increment unyieldable-depth: yields from __close are forbidden.
                          ;; This ensures coroutine.yield() inside __close throws
                          ;; "attempt to yield" rather than actually yielding.
                          (binding [coro/*unyieldable-depth* (unchecked-inc (long coro/*unyieldable-depth*))]
                            (call-function-from-stack mm call-args env))
                          nil
                          (catch ExceptionInfo e
                            ;; Append "\nin metamethod 'close'" only for string errors.
                            ;; Non-string error values (integers, tables) are kept as-is
                            ;; per Lua 5.5 semantics (pcall returns the raw error value).
                            (let [data (ex-data e)
                                  lua-err (when (contains? data :lua-error) (:lua-error data))]
                              (if (or (nil? lua-err) (string? lua-err))
                                (let [close-msg (str (ex-message e) "\nin metamethod 'close'")]
                                  (ex-info close-msg (assoc data :lua-error close-msg)))
                                e)))
                          (catch Exception e
                            (let [close-msg (str (ex-message e) "\nin metamethod 'close'")]
                              (ex-info close-msg {:type :error :lua-error close-msg})))
                          (finally
                            ;; Fire return hook for the __close metamethod, matching Lua 5.5
                            ;; semantics where return hooks fire when close fns complete.
                            (fire-hook! env "return" nil)
                            (env/pop-stack-frame! env)))]
            (recur (rest items) (or new-err current-err)))
          ;; mm is nil: __close was removed after variable was bound — error
          (let [missing-err (ex-info "missing metamethod 'close'"
                                     {:type :error :lua-error "missing metamethod 'close'"})]
            (recur (rest items) (or missing-err current-err))))))))

(defn close-block-normal!
  "Run a block frame's close-list for a normal (non-error) scope exit.
  Marks the close-list as consumed (close-list-ran? = true) and throws
  the final error if any __close metamethod failed."
  [frame env]
  (let [close-list (:close-list frame)
        ran? (:close-list-ran? frame)]
    (when ran? (reset! ran? true))
    (when (seq close-list)
      (when-let [err (run-close-list! close-list env nil)]
        (throw err)))))

(defn close-for-backward-goto!
  "Close to-be-closed variables that go out of scope when goto jumps backward
  to target-idx.  Entries in close-list are [value stmt-index name] triples;
  those with stmt-index > target-idx are closed (LIFO order, already maintained
  by the prepend-on-declare convention), their names removed from env, and the
  entries dropped from the list.
  Returns the updated close-list (only entries with stmt-index <= target-idx)."
  [close-list target-idx env]
  (let [ti (long target-idx)
        to-close (filter #(> (long (second %)) ti) close-list)
        remaining (remove #(> (long (second %)) ti) close-list)]
    (when (seq to-close)
      (when-let [err (run-close-list! to-close env nil)]
        (throw err)))
    (doseq [[_ _ name] to-close]
      (when name (env/undeclare! env name)))
    remaining))

(defn- apply-native-pcall-error
  "Apply pcall/xpcall error semantics for errors from a native body function.
  Returns the wrapped error result vector."
  [outer-wrap msgh env err-ex]
  (let [err-val (extract-lua-error err-ex)]
    (case outer-wrap
      :xpcall-pcall [true false err-val]
      :xpcall (loop [cur-err err-val
                     depth 0]
                (if (>= depth 200)
                  [false "C stack overflow"]
                  (let [[ok? v] (try
                                  (let [r (call-function-from-stack msgh [cur-err] env)]
                                    [true (if (vector? r) (first r) r)])
                                  (catch Exception e
                                    [false (extract-lua-error e)]))]
                    (if ok?
                      [false v]
                      ;; If handler raised "C stack overflow", it overflowed — stop retrying
                      (if (= v "C stack overflow")
                        [false "error in error handling"]
                        (recur v (inc depth)))))))
      [false err-val])))

(defn- recover-frames-loop
  "Inner loop for error recovery. Walks remaining stack frames looking for
  a :pcall-frame to deliver the error, running __close metamethods on :block
  and :for-generic-loop frames along the way.

  When a block with a non-empty close-list is encountered, switches to the
  async path: returns [:continue [error-propagation-frame close-list-runner-frame]]
  so the stack machine can yield through __close metamethods.

  Returns:
  - [:continue new-stack] - pcall found (or async runner pushed), continue
  - {:type :done :value v} - pcall found with no parent stack
  - [:propagate err] - no pcall found"
  [stack err-ex self-close?]
  (loop [remaining stack
         current-err err-ex]
    (if (empty? remaining)
      [:propagate current-err]
      (let [f (peek remaining)
            rest-stack (pop remaining)]
        (cond
          ;; pcall-frame: wrap and deliver the error (or skip for self-close).
          (= :pcall-frame (:type f))
          (if self-close?
            (do (when-let [e (:pcall-call-env f)] (env/pop-stack-frame! e))
                (recur rest-stack current-err))
            (let [_ (when-let [e (:pcall-call-env f)] (env/pop-stack-frame! e))
                  err-val (extract-lua-error current-err)
                  outer-wrap (:outer-wrap f)
                  msgh (:msgh f)
                  pcall-env (:env f)
                  wrapped (case outer-wrap
                            :xpcall-pcall [true false err-val]
                            :xpcall (try
                                      (let [r (call-function-from-stack msgh [err-val] pcall-env)]
                                        [false (if (vector? r) (first r) r)])
                                      (catch Exception _
                                        [false "error in error handling"]))
                            [false err-val])]
              (if (empty? rest-stack)
                {:type :done :value wrapped}
                [:continue (set-frame-result rest-stack wrapped)])))

          ;; Block frame: run close-list asynchronously (via runner) if non-empty,
          ;; or skip synchronously if empty or already ran.
          ;; For function-body blocks, pop the call stack frame BEFORE running __close
          ;; so that debug.getinfo(2) sees the pcall frame, not the function that errored.
          (= :block (:type f))
          (let [ran? (:close-list-ran? f)
                close-list (:close-list f)
                frame-env (:env f)
                _ (pop-call-stack-if-needed! f)
                ;; Skip if already ran (atom true) OR if the block is in :closing state
                ;; (:closing means runner already executed the list; prevents double-run)
                already-ran (or (and ran? @ran?) (= :closing (:state f)))]
            (if (and (not already-ran) (seq close-list))
              ;; Decide whether to run __close asynchronously (yieldable) or
              ;; synchronously (non-yieldable). Use :unyieldable-context in the
              ;; exception to detect errors thrown from within native callbacks
              ;; (e.g. string.gsub, table.sort) where yields are forbidden.
              (let [unyieldable? (:unyieldable-context (ex-data current-err))]
                (if unyieldable?
                  ;; Sync path: non-yieldable context — run-close-list! increments
                  ;; *unyieldable-depth* internally, so yields are still blocked.
                  (do
                    (when ran? (reset! ran? true))
                    (let [new-err (or (run-close-list! close-list frame-env current-err)
                                      current-err)]
                      (recur rest-stack new-err)))
                  ;; Async path: yieldable context — push close-list-runner so
                  ;; __close metamethods can yield during error propagation.
                  (do
                    (when ran? (reset! ran? true))
                    [:continue [(make-error-propagation-frame rest-stack self-close? frame-env)
                                (make-close-list-runner-frame close-list frame-env current-err)]])))
              ;; Empty close-list or already ran: skip.
              (recur rest-stack current-err)))

          ;; For-generic loop: run __close on the to-be-closed 4th iterator value.
          (= :for-generic-loop (:type f))
          (let [close-val (:close-val f)
                frame-env (:env f)]
            (if (and close-val (not (false? close-val)))
              (let [unyieldable? (:unyieldable-context (ex-data current-err))]
                (if unyieldable?
                  ;; Sync path: non-yieldable context.
                  (let [new-err (or (run-close-list! [close-val] frame-env current-err)
                                    current-err)]
                    (recur rest-stack new-err))
                  ;; Async path: yieldable context.
                  [:continue [(make-error-propagation-frame rest-stack self-close? frame-env)
                              (make-close-list-runner-frame [close-val] frame-env current-err)]]))
              ;; No close value: skip.
              (recur rest-stack current-err)))

          ;; Close-list runner frame: absorb the error (runner handles __close errors
          ;; internally by updating current-err and continuing with remaining items).
          (= :close-list-runner (:type f))
          [:continue (push-frame rest-stack (assoc f :state :after-call
                                                      :call-error current-err))]

          ;; Error-propagation frame: its remaining stack was already processed
          ;; (the handler returned [:error ...] meaning no pcall was found there);
          ;; just pop and continue with what's below it.
          (= :error-propagation (:type f))
          (recur rest-stack current-err)

          :else
          (recur rest-stack current-err))))))

(defn- recover-from-pcall
  "Try to recover from an error by finding a :pcall-frame in the stack.
  While scanning, runs __close metamethods on any block frames that have
  unconsumed close-lists (in LIFO scope order). When a block with a non-empty
  close-list is encountered, switches to an async path so that __close
  metamethods can yield during error propagation.
  Returns:
  - [:continue new-stack] - pcall found (or async runner pushed), continue
  - {:type :done :value v} - pcall found with no parent stack
  - [:propagate err] - no pcall found

  Special case: :self-close and :exit errors skip all pcall-frames.
  (:self-close = coroutine.close() self-close; :exit = os.exit()).
  Block close-lists still run normally."
  [stack err-ex]
  (let [t (:type (ex-data err-ex))
        self-close? (or (= :self-close t) (= :exit t))]
    (recover-frames-loop stack err-ex self-close?)))

(defn- error-location-from-frame
  "Get [line source] for an error from the current frame's env and node."
  [frame]
  (let [frame-env (:env frame)
        node-line (when-let [n (:node frame)] (:line n))
        env-line (when frame-env (when-let [a (:current-line frame-env)] @a))
        line (or node-line env-line)
        source (when frame-env (or (:chunk-name frame-env) (:source frame-env)))]
    [line source]))

(defn handle-eval-exp-with-yield
  "Wrapper around handle-eval-exp that catches yield and error exceptions.
  Converts :coro-yield exceptions to [:yield ...] results.
  Converts all other ExceptionInfo and StackOverflowError to [:error e] results,
  so that run-stack-machine can apply pcall-frame error recovery.
  Attaches :error-line/:error-source to runtime errors (non-:lua-error) so that
  extract-lua-error can prepend the 'source:line: ' prefix for pcall recovery."
  [stack frame]
  ;; Update position from the node on each frame evaluation for expression-level
  ;; line tracking (needed for accurate lineerror() line numbers).
  (when-let [n (:node frame)]
    (when-let [e (:env frame)]
      (expr/update-position! n e)))
  (try
    (handle-eval-exp stack frame)
    (catch ExceptionInfo e
      (if (= :coro-yield (:type (ex-data e)))
        [:yield {:values (:values (ex-data e))
                 :stack stack}]
        (let [data (ex-data e)]
          ;; If already has :lua-error or :error-line, return as-is
          (if (or (contains? data :lua-error) (contains? data :error-line))
            [:error e]
            ;; Runtime error: attach location info for extract-lua-error
            (let [[line source] (error-location-from-frame frame)]
              [:error (ex-info (ex-message e)
                               (assoc data :error-line line :error-source source))])))))
    (catch StackOverflowError _
      (let [[line source] (error-location-from-frame frame)]
        [:error (ex-info "C stack overflow"
                         {:type :error :error-line line :error-source source})]))
    (catch Exception e
      (let [[line source] (error-location-from-frame frame)]
        [:error (ex-info (or (ex-message e) "error")
                         {:type :error :error-line line :error-source source})]))))

(defn run-stack-machine
  "Execute the stack machine until completion or yield.

  Returns:
  - {:type :done, :value v} - Execution completed
  - {:type :yield, :values [...], :stack stack} - Yielded, save stack
  - {:type :error, :error e} - Error occurred"
  [initial-stack env]
  (loop [stack initial-stack
         iteration 0]
    ;; SM iteration limit = 100× the env step-limit (each env step ~ 10-20 SM iterations).
    ;; Falls back to 1 billion to guard against SM bugs when env step-limit is very small.
    (when (> iteration (max 1000000000 (* 100 (long (or (:step-limit env) 1000000)))))
      (throw (ex-info "Stack machine iteration limit exceeded"
                      {:stack stack})))

    (cond
      ;; Empty stack means we're done
      (empty? stack)
      {:type :done :value nil}

      ;; Process top frame
      :else
      (let [frame (peek stack)]
        (case (:type frame)
          ;; Evaluate expression
          :eval-exp
          (let [[action result] (handle-eval-exp-with-yield stack frame)]
            (case action
              :done {:type :done :value (:value result)}
              :continue (recur result (inc iteration))
              :yield {:type :yield
                      :values (:values result)
                      :stack (:stack result)}
              :error (let [recovery (recover-from-pcall stack result)]
                       (cond
                         (not (vector? recovery)) recovery  ; {:type :done ...}
                         (= :continue (first recovery)) (recur (second recovery) (inc iteration))
                         :else {:type :error :error (second recovery)}))))

          ;; Metamethod call - dispatch using handle-eval-exp
          :metamethod-call
          (let [[action result] (handle-eval-exp-with-yield stack frame)]
            (case action
              :done {:type :done :value (:value result)}
              :continue (recur result (inc iteration))
              :yield {:type :yield
                      :values (:values result)
                      :stack (:stack result)}
              :error (let [recovery (recover-from-pcall stack result)]
                       (cond
                         (not (vector? recovery)) recovery  ; {:type :done ...}
                         (= :continue (first recovery)) (recur (second recovery) (inc iteration))
                         :else {:type :error :error (second recovery)}))))

          ;; Block execution - dispatch using handle-eval-exp
          :block
          (let [[action result] (handle-eval-exp-with-yield stack frame)]
            (case action
              :done {:type :done :value (:value result)}
              :continue (recur result (inc iteration))
              :yield {:type :yield
                      :values (:values result)
                      :stack (:stack result)}
              :error (let [recovery (recover-from-pcall stack result)]
                       (cond
                         (not (vector? recovery)) recovery  ; {:type :done ...}
                         (= :continue (first recovery)) (recur (second recovery) (inc iteration))
                         :else {:type :error :error (second recovery)}))))

          ;; While loop frame
          :while-loop
          (let [[action result] (handle-eval-exp-with-yield stack frame)]
            (case action
              :done {:type :done :value (:value result)}
              :continue (recur result (inc iteration))
              :yield {:type :yield
                      :values (:values result)
                      :stack (:stack result)}
              :error (let [recovery (recover-from-pcall stack result)]
                       (cond
                         (not (vector? recovery)) recovery  ; {:type :done ...}
                         (= :continue (first recovery)) (recur (second recovery) (inc iteration))
                         :else {:type :error :error (second recovery)}))))

          ;; For-numeric loop frame
          :for-numeric-loop
          (let [[action result] (handle-eval-exp-with-yield stack frame)]
            (case action
              :done {:type :done :value (:value result)}
              :continue (recur result (inc iteration))
              :yield {:type :yield
                      :values (:values result)
                      :stack (:stack result)}
              :error (let [recovery (recover-from-pcall stack result)]
                       (cond
                         (not (vector? recovery)) recovery  ; {:type :done ...}
                         (= :continue (first recovery)) (recur (second recovery) (inc iteration))
                         :else {:type :error :error (second recovery)}))))

          ;; For-generic loop frame
          :for-generic-loop
          (let [[action result] (handle-eval-exp-with-yield stack frame)]
            (case action
              :done {:type :done :value (:value result)}
              :continue (recur result (inc iteration))
              :yield {:type :yield
                      :values (:values result)
                      :stack (:stack result)}
              :error (let [recovery (recover-from-pcall stack result)]
                       (cond
                         (not (vector? recovery)) recovery  ; {:type :done ...}
                         (= :continue (first recovery)) (recur (second recovery) (inc iteration))
                         :else {:type :error :error (second recovery)}))))

          ;; Repeat loop frame
          :repeat-loop
          (let [[action result] (handle-eval-exp-with-yield stack frame)]
            (case action
              :done {:type :done :value (:value result)}
              :continue (recur result (inc iteration))
              :yield {:type :yield
                      :values (:values result)
                      :stack (:stack result)}
              :error (let [recovery (recover-from-pcall stack result)]
                       (cond
                         (not (vector? recovery)) recovery  ; {:type :done ...}
                         (= :continue (first recovery)) (recur (second recovery) (inc iteration))
                         :else {:type :error :error (second recovery)}))))

          ;; pcall-frame: protected call running body as stack machine sub-frames
          :pcall-frame
          (let [[action result] (handle-eval-exp-with-yield stack frame)]
            (case action
              :done {:type :done :value (:value result)}
              :continue (recur result (inc iteration))
              :yield {:type :yield
                      :values (:values result)
                      :stack (:stack result)}
              :error (let [recovery (recover-from-pcall stack result)]
                       (cond
                         (not (vector? recovery)) recovery  ; {:type :done ...}
                         (= :continue (first recovery)) (recur (second recovery) (inc iteration))
                         :else {:type :error :error (second recovery)}))))

          ;; Close-list runner frame
          :close-list-runner
          (let [[action result] (handle-eval-exp-with-yield stack frame)]
            (case action
              :done {:type :done :value (:value result)}
              :continue (recur result (inc iteration))
              :yield {:type :yield
                      :values (:values result)
                      :stack (:stack result)}
              :error (let [recovery (recover-from-pcall stack result)]
                       (cond
                         (not (vector? recovery)) recovery  ; {:type :done ...}
                         (= :continue (first recovery)) (recur (second recovery) (inc iteration))
                         :else {:type :error :error (second recovery)}))))

          ;; Error-propagation frame (async error recovery after __close runner)
          :error-propagation
          (let [[action result] (handle-eval-exp-with-yield stack frame)]
            (case action
              :done {:type :done :value (:value result)}
              :continue (recur result (inc iteration))
              :yield {:type :yield
                      :values (:values result)
                      :stack (:stack result)}
              :error (let [recovery (recover-from-pcall stack result)]
                       (cond
                         (not (vector? recovery)) recovery  ; {:type :done ...}
                         (= :continue (first recovery)) (recur (second recovery) (inc iteration))
                         :else {:type :error :error (second recovery)}))))

          ;; Unknown frame type
          (throw (ex-info "Unknown frame type"
                          {:frame frame})))))))
;; Helper to get final result from :done
(defn get-result
  "Extract the final result value from a completed run."
  [run-result]
  (case (:type run-result)
    :done (:value run-result)
    :yield (throw (ex-info "Cannot get result from yielded execution"
                           {:result run-result}))
    :error (throw (:error run-result))))

;;; Integration with existing interpreter

(defn eval-exp-with-stack
  "Evaluate an expression using the stack machine.
  This will eventually replace eval-exp for coroutine contexts."
  [node env]
  (binding [env/*global-scope* (:global-scope env)]
    (let [initial-stack [(make-eval-exp-frame node env)]
          result (run-stack-machine initial-stack env)]
      (get-result result))))
