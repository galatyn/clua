(ns clua.interpreter.coro-runtime
  "Coroutine runtime support for CLua using state machine approach.

   Coroutines are implemented by transforming yieldable functions into
   state machines that can suspend and resume execution. Instead of
   rewriting the entire interpreter in CPS style, we only instrument
   code paths that contain yields or call yieldable functions.")

(set! *warn-on-reflection* true)

;;; Dynamic vars

(def ^:dynamic *in-hook*
  "True when a debug hook is currently executing.
   Prevents re-entrant hook firing."
  false)

;;; Coroutine state structures

(defn make-coroutine-state
  "Create a new coroutine state.

   State contains:
   - :status - :suspended, :running, :dead, or :normal
   - :function - the Lua function being executed
   - :call-stack - stack of activation frames for nested calls
   - :resume-values - values passed to resume (used as yield return values)"
  [lua-function]
  {:type :lua-coroutine
   :status :suspended
   :function lua-function
   :call-stack []
   :resume-values nil})

(defn coroutine-suspended? [coro-state]
  (= :suspended (:status coro-state)))

(defn coroutine-running? [coro-state]
  (= :running (:status coro-state)))

(defn coroutine-dead? [coro-state]
  (= :dead (:status coro-state)))

;;; Resume point analysis

(defn yield-call?
  "Check if an AST node is a call to coroutine.yield."
  [node]
  (and (map? node)
       (= :function-call (:type node))
       (let [target (:target node)]
         (and (= :field-access (:type target))
              (= :name (:type (:object target)))
              (= "coroutine" (:value (:object target)))
              (= :name (:type (:field target)))
              (= "yield" (:value (:field target)))))))

(defn has-function-call?
  "Recursively check if an AST node contains a function call.
   This is conservative - returns true if there might be a call."
  [node]
  (cond
    (nil? node) false
    (not (map? node)) false

    ;; Direct function/method calls
    (#{:function-call :method-call} (:type node)) true

    ;; Recurse into child nodes
    :else
    (some has-function-call? (vals node))))

(defn statement-needs-label?
  "Check if a statement needs a resume label.
   Returns true if the statement:
   - Contains a yield call
   - Contains any function call (which might yield)"
  [stmt]
  (or (yield-call? stmt)
      (has-function-call? stmt)))

(defn find-resume-points
  "Analyze a block's statements and assign labels to resume points.

   Returns a map: {statement-index -> label-number}

   Labeling scheme:
   - ALL statements before the first yield/call get label 0
   - First yield/call gets label 1, next statement gets label 2
   - Subsequent yields/calls follow the pattern (label N, N+1)

   This eliminates ambiguity between 'fresh start' and 'resume at first yield'."
  [statements]
  (loop [idx 0
         label-num 0
         labels {}
         found-first-resume-point? false]
    (if (>= idx (count statements))
      labels
      (let [stmt (nth statements idx)]
        (if (not found-first-resume-point?)
          ;; Before first yield/call: assign everything label 0
          (if (statement-needs-label? stmt)
            ;; This is the first yield/call, label it 1, next is 2
            (recur (inc idx)
                   3
                   (-> labels
                       (assoc idx 1)
                       (assoc (inc idx) 2))
                   true)
            ;; Not a yield/call yet, label it 0
            (recur (inc idx)
                   0
                   (assoc labels idx 0)
                   false))
          ;; After first yield/call: use the standard scheme
          (if (statement-needs-label? stmt)
            (recur (inc idx)
                   (+ label-num 2)
                   (-> labels
                       (assoc idx label-num)
                       (assoc (inc idx) (inc label-num)))
                   true)
            ;; No label needed (rare after first yield)
            (recur (inc idx)
                   label-num
                   labels
                   true)))))))

(defn body-has-yield?
  "Check if a function body contains any yield calls.
   This is a deep analysis that checks all nested blocks."
  [body]
  (cond
    (nil? body) false
    (not (map? body)) false

    ;; Check if this is a yield call
    (yield-call? body) true

    ;; Check statements in a block
    (= :block (:type body))
    (some body-has-yield? (:statements body))

    ;; Recurse into all child nodes
    :else
    (some body-has-yield? (vals body))))

(defn annotate-block-resume-points
  "Annotate a block node with pre-computed resume points.
   Returns the block with :resume-points added."
  [block]
  (if (and (map? block) (= :block (:type block)))
    (let [statements (:statements block)
          resume-points (find-resume-points statements)]
      (assoc block :resume-points resume-points))
    block))

(defn annotate-resume-points
  "Recursively walk an AST node and annotate all blocks with resume points.
   This pre-computes resume points once at function creation time."
  [node]
  (cond
    (nil? node) nil
    (not (map? node)) node

    ;; This is a block - annotate it and recurse into statements
    (= :block (:type node))
    (let [annotated-block (annotate-block-resume-points node)
          ;; Recursively annotate nested blocks in statements
          annotated-statements (mapv annotate-resume-points (:statements annotated-block))]
      (assoc annotated-block :statements annotated-statements))

    ;; For other map nodes, recursively process all values
    :else
    (reduce-kv
      (fn [acc k v]
        (assoc acc k (cond
                       (map? v) (annotate-resume-points v)
                       (vector? v) (mapv annotate-resume-points v)
                       :else v)))
      node
      node)))

(defn mark-yieldable
  "Mark a Lua function as yieldable if it contains yields.
   Pre-computes resume points for all blocks in the function body.
   This is metadata used by the interpreter to decide whether to
   use the resumable execution path."
  [lua-function]
  (if (body-has-yield? (:body lua-function))
    (let [annotated-body (annotate-resume-points (:body lua-function))]
      (assoc lua-function
        :yieldable true
        :body annotated-body))
    lua-function))

;;; Result types for resumable execution

(defn result-continue
  "Create a result indicating normal statement completion."
  ([] (result-continue {}))
  ([locals]
   {:result-type :continue
    :locals locals}))

(defn result-yielded
  "Create a result indicating the coroutine yielded."
  ([values pc locals env]
   (result-yielded values pc locals env []))
  ([values pc locals env call-stack]
   {:result-type :yielded
    :values values
    :pc pc
    :locals locals
    :env env
    :call-stack call-stack}))

(defn result-returned
  "Create a result indicating the function returned."
  ([] (result-returned nil nil))
  ([values] (result-returned values nil))
  ([values tail-call]
   (if tail-call
     {:result-type :returned
      :values values
      :tail-call tail-call}
     {:result-type :returned
      :values values})))

;;; Main thread representation

(def main-thread
  "The main thread coroutine object.
   Returned by coroutine.running() when not executing inside a coroutine.
   Status is always :running since the main thread is always active from its own perspective.
   coroutine.resume(main-thread) returns false (cannot resume a running thread)."
  {:type :lua-coroutine
   :main-thread true
   :state (atom {:type :lua-coroutine
                 :status :running
                 :main-thread true
                 :function nil
                 :call-stack []
                 :resume-values nil})})

;;; Dynamic var for tracking current coroutine context

(def ^:dynamic *current-coroutine*
  "The currently executing coroutine state, or nil if running in main thread."
  nil)

(def ^:dynamic *unyieldable-depth*
  "Depth of non-yieldable native (Clojure) callbacks currently on the call stack.
   Incremented when a stdlib function invokes a Lua callback synchronously
   (e.g. string.gsub replacement function, table.sort comparator). When > 0,
   coroutine.isyieldable() returns false even inside a coroutine."
  0)

(defn in-coroutine?
  "Check if we're currently executing inside a coroutine."
  []
  (some? *current-coroutine*))

(defn is-yieldable?
  "Check if the current execution context can yield.
   Returns false when inside a non-yieldable native callback even if a
   coroutine is active."
  []
  (and (some? *current-coroutine*) (zero? (long *unyieldable-depth*))))

(defn get-current-coroutine
  "Get the current coroutine state, or nil if not in a coroutine."
  []
  *current-coroutine*)
