(ns clua.stdlib.coroutine
  "Coroutine manipulation library for CLua.

   Implements Lua 5.4 coroutine API."
  (:require [clua.interpreter.coro-runtime :as coro]
            [clua.interpreter.env :as env])
  (:import (clojure.lang ExceptionInfo)))
(set! *warn-on-reflection* true)


;; Forward declare interpreter functions
(declare make-table table-set!)

(defn coroutine-create
  "Create a new coroutine from a function.

   Usage: coroutine.create(f)
   Returns: coroutine object (with mutable state in atom)"
  [func]
  (when-not (or (fn? func)
                (and (map? func) (= :lua-function (:type func))))
    (throw (ex-info "coroutine.create: argument must be a function"
                    {:type :type-error})))

  ;; Mark Lua functions as yieldable; the SM handles yield/resume natively
  ;; via the resume-values-set mechanism, so no CPS transformation is needed.
  (let [transformed-func (if (and (map? func) (= :lua-function (:type func)))
                           (assoc func :yieldable true)
                           func)]
    ;; Create a coroutine state wrapped in an atom for mutability
    {:type :lua-coroutine
     :state (atom (coro/make-coroutine-state transformed-func))}))

(defn- run-sm-result
  "Process a stack machine result from a coroutine first-run or resume."
  [sm-result running-coro state-atom coro-env]
  (case (:type sm-result)
    :done
    (do
      (reset! state-atom (assoc running-coro :status :dead :call-stack []))
      (let [v (:value sm-result)]
        (cond
          (nil? v) [true]
          (vector? v) (into [true] v)
          :else [true v])))
    :yield
    (let [saved-stack (:stack sm-result)
          suspended-coro (-> running-coro
                             (assoc :status :suspended)
                             (assoc :expr-stack saved-stack)
                             (assoc :call-stack []))]
      (reset! state-atom suspended-coro)
      (let [yield-vals (:values sm-result)]
        (cond
          (nil? yield-vals) [true]
          (vector? yield-vals) (into [true] yield-vals)
          :else [true yield-vals])))
    :error
    (let [^Throwable err-ex (:error sm-result)
          err-data (ex-data err-ex)]
      (if (= :self-close (:type err-data))
        ;; Self-close completed with no __close error: normal coroutine death
        (do (reset! state-atom (assoc running-coro :status :dead :call-stack []))
            [true])
        (let [err-val (if (and err-data (contains? err-data :lua-error))
                        (:lua-error err-data)
                        (str (.getMessage err-ex)))
              ;; Prefer snapshot captured at throw-time (includes native 'error' frame).
              ;; Fall back to reading the coro-env call-stack atom for non-lua-error exceptions.
              saved-cs (or (:error-call-stack err-data)
                           (some-> coro-env :call-stack deref vec)
                           [])]
          (reset! state-atom (assoc running-coro :status :dead
                                                 :saved-call-stack saved-cs
                                                 :lua-error err-val))
          [false err-val])))))

(defn- resume-first-run
  "Handle the first resume of a coroutine (initial call)."
  [func values state-atom running-coro]
  (cond
    (= :lua-function (:type func))
    ;; Lua function: run directly via stack machine
    (let [sm-ns (find-ns 'clua.interpreter.stack-machine)
          make-fn-frame (ns-resolve sm-ns 'make-function-block-frame)
          run-sm (ns-resolve sm-ns 'run-stack-machine)
          coro-joins (env/get-upvalue-joins func)
          ;; Each coroutine gets its own call-stack and hook atoms so that
          ;; debug inspection of a coroutine does not mix with the main thread.
          ;; outer-scope-count must be set so enumerate-locals finds the correct
          ;; param-scope (the scope pushed here) vs captured upvalue scopes.
          outer-scope-count (count (:scopes (:env func)))
          ;; Pick up any pending hook set via debug.sethook(co,...) before first resume
          pending-hook (:pending-hook running-coro)
          base-coro-env (assoc (env/push-scope (:env func))
                          :outer-scope-count outer-scope-count
                          :call-stack (atom [])
                          :hook (atom pending-hook)
                          :current-line (atom nil)
                          :current-column (atom nil))
          func-env (if coro-joins (assoc base-coro-env :upvalue-joins coro-joins) base-coro-env)
          params (:params func)
          has-varargs (:varargs func)
          num-params (count params)
          _ (doseq [[param-name arg-val] (map vector params values)]
              (env/define! func-env param-name arg-val))
          _ (when has-varargs
              (env/define! func-env "..." (vec (drop num-params values))))
          stmts (:statements (:body func))
          ;; env-atom is updated before each statement so debug.getlocal(co, level, n) works
          env-atom (atom func-env)
          ;; Push a call-stack frame for the coroutine body so debug.getlocal can find locals.
          ;; :call-fn-env causes pop-call-stack-if-needed! on normal exit.
          _ (env/push-stack-frame! func-env (:name func) 0 0 func env-atom)
          fire-hook! (ns-resolve sm-ns 'fire-hook!)
          block-frame (assoc (make-fn-frame stmts func-env)
                        :call-fn-env func-env
                        :frame-env-atom env-atom)
          ;; Fire "call" hook for the coroutine body function itself.
          ;; This mirrors what happens in the function-call SM handler for regular calls.
          _ (when fire-hook! (fire-hook! func-env "call" nil))
          sm-result (binding [env/*current-env* func-env]
                      (run-sm [block-frame] func-env))]
      (run-sm-result sm-result running-coro state-atom func-env))

    ;; pcall/xpcall as coroutine body: run through stack machine as a pcall-frame
    ;; so yields from the body propagate correctly (e.g. coroutine.create(pcall)).
    (or (:clua/pcall (meta func)) (:clua/xpcall (meta func)))
    (let [sm-ns (find-ns 'clua.interpreter.stack-machine)
          run-sm (ns-resolve sm-ns 'run-stack-machine)
          pcall? (:clua/pcall (meta func))
          coro-env (assoc env/*current-env*
                     :call-stack (atom [])
                     :hook (atom nil)
                     :current-line (atom nil)
                     :current-column (atom nil))
          pcall-frame (if pcall?
                        {:type :pcall-frame :state :run-body
                         :body-fn (first values)
                         :body-args (vec (rest values))
                         :env coro-env}
                        ;; xpcall(handler, body, args...)
                        {:type :pcall-frame :state :run-body
                         :body-fn (second values)
                         :body-args (vec (drop 2 values))
                         :outer-wrap :xpcall
                         :msgh (first values)
                         :env coro-env})
          sm-result (binding [env/*current-env* coro-env]
                      (run-sm [pcall-frame] coro-env))]
      (run-sm-result sm-result running-coro state-atom coro-env))

    ;; Native function: use call-function (no SM needed)
    :else
    (let [interp-ns (find-ns 'clua.interpreter.core)
          call-function (ns-resolve interp-ns 'call-function)
          result (try
                   {:result-type :returned
                    :values (call-function func values env/*current-env*)}
                   (catch ExceptionInfo e
                     (if (= :coro-yield (:type (ex-data e)))
                       (let [ex-data-map (ex-data e)
                             yield-state (or (:pending-yield-state @state-atom)
                                             {:values (:values ex-data-map)})]
                         (swap! state-atom dissoc :pending-yield-state)
                         {:result-type :yielded
                          :values (:values yield-state)})
                       (throw e))))]
      (case (:result-type result)
        :returned
        (do
          (reset! state-atom (assoc running-coro :status :dead :call-stack []))
          (let [ret-values (:values result)]
            (cond
              (nil? ret-values) [true]
              (vector? ret-values) (into [true] ret-values)
              :else [true ret-values])))
        :yielded
        (let [;; call-function saves the inner Lua SM stack in :pending-inner-stack
              ;; when a Lua fn called by this native fn yields.
              saved-stack (:pending-inner-stack @state-atom)
              yield-vals (:values result)]
          (swap! state-atom dissoc :pending-inner-stack)
          (if saved-stack
            ;; Native fn called a yieldable Lua fn — save SM state so we can resume it
            (do
              (reset! state-atom (-> running-coro
                                     (assoc :status :suspended :call-stack [])
                                     (assoc :expr-stack saved-stack)))
              (cond
                (nil? yield-vals) [true]
                (vector? yield-vals) (into [true] yield-vals)
                :else [true yield-vals]))
            ;; No saved inner stack — native fn cannot be resumed
            (do
              (reset! state-atom (assoc running-coro :status :dead :call-stack []))
              [false "cannot resume dead coroutine"])))
        (do
          (reset! state-atom (assoc running-coro :status :dead :call-stack []))
          [false "unknown result type"])))))

(defn- execute-resume
  "Execute the resume of a coroutine from a saved stack machine state."
  [_frame _func running-coro state-atom]
  (let [expr-stack (:expr-stack running-coro)
        func-env (-> expr-stack peek :env)
        stack-machine-ns (find-ns 'clua.interpreter.stack-machine)
        run-stack-machine (ns-resolve stack-machine-ns 'run-stack-machine)
        _ (swap! state-atom assoc :resume-values-set true)
        sm-result (binding [env/*current-env* func-env]
                    (run-stack-machine expr-stack func-env))]
    (run-sm-result sm-result running-coro state-atom func-env)))


(defn- handle-error-exception
  "Handle an error exception from coroutine execution.
   Preserves the original Lua error value (not just message string) for pcall recovery."
  [^Throwable e running-coro state-atom coro-env]
  (let [data (ex-data e)
        err-val (if (and data (contains? data :lua-error))
                  (:lua-error data)
                  (str (.getMessage e)))
        saved-cs (or (:error-call-stack data)
                     (some-> coro-env :call-stack deref vec)
                     [])]
    (reset! state-atom (assoc running-coro :status :dead :call-stack []
                                           :saved-call-stack saved-cs
                                           :last-error (.getMessage e)
                                           :lua-error err-val))
    [false err-val]))

(defn coroutine-resume
  "Resume a suspended coroutine, passing values to it.

   Usage: coroutine.resume(co, val1, ...)
   Returns: true, value1, value2, ... on success
            false, error-message on error"
  [coro & values]
  ;; Validate coroutine
  (when-not (and (map? coro) (= :lua-coroutine (:type coro)))
    (throw (ex-info "coroutine.resume: first argument must be a coroutine"
                    {:type :type-error})))

  (let [state-atom (:state coro)
        coro-state @state-atom]

    (cond
      ;; Can't resume dead coroutine
      (coro/coroutine-dead? coro-state)
      [false "cannot resume dead coroutine"]

      ;; Can't resume running coroutine
      (coro/coroutine-running? coro-state)
      [false "cannot resume non-suspended coroutine"]

      ;; Resume suspended coroutine
      (coro/coroutine-suspended? coro-state)
      (let [func (:function coro-state)
            ;; True first run: no saved expr-stack
            first-run? (not (:expr-stack coro-state))
            ;; For resume of suspended coro: env is in the saved expr-stack
            resume-coro-env (when-not first-run?
                              (-> coro-state :expr-stack peek :env))
            ;; No need for resume-values-set flag since we skip past yield with PC
            running-coro (-> coro-state
                             (assoc :status :running)
                             (assoc :resume-values values))]

        ;; Update atom with running state
        (reset! state-atom running-coro)

        ;; Mark calling coroutine (or main thread) as :normal while we execute this one
        (let [calling-coro (coro/get-current-coroutine)
              calling-state-atom (if calling-coro
                                   (:state calling-coro)
                                   (:state coro/main-thread))
              calling-prev-status (when calling-state-atom (:status @calling-state-atom))]
          (when calling-state-atom
            (swap! calling-state-atom assoc :status :normal))
          (try
            ;; Execute the coroutine function in coroutine context
            (let [result (binding [coro/*current-coroutine* coro]
                           (if first-run?
                             (resume-first-run func values state-atom running-coro)
                             (execute-resume nil func running-coro state-atom)))]
              ;; Restore calling coroutine status
              (when calling-state-atom
                (swap! calling-state-atom assoc :status (or calling-prev-status :running)))
              result)

            (catch ExceptionInfo e
              ;; Restore calling coroutine status on error too
              (when calling-state-atom
                (swap! calling-state-atom assoc :status (or calling-prev-status :running)))
              (handle-error-exception e running-coro state-atom resume-coro-env)))))

      ;; Unknown status
      :else
      [false "invalid coroutine status"])))

(defn coroutine-yield
  "Yield from the current coroutine.

   Usage: coroutine.yield(val1, val2, ...)
   Returns: values passed to resume"
  [& values]
  ;; Check if we're in a coroutine
  (if-let [current-coro (coro/get-current-coroutine)]
    ;; Check if we're resuming (resume-values key exists, even if value is nil/empty)
    (let [_ (when (pos? (long coro/*unyieldable-depth*))
              (throw (ex-info "attempt to yield across a C-call boundary"
                              {:type :error :lua-error "attempt to yield across a C-call boundary"})))
          coro-state @(:state current-coro)
          resume-vals (:resume-values coro-state)
          resuming? (contains? coro-state :resume-values-set)]
      (if resuming?
        ;; Resuming - return the resume values instead of yielding
        ;; Clear the resuming flag so next yield will actually yield
        (do
          (swap! (:state current-coro) dissoc :resume-values-set)
          (cond
            (nil? resume-vals) nil
            (and (seqable? resume-vals) (empty? resume-vals)) nil
            (and (seqable? resume-vals) (= 1 (count resume-vals))) (first resume-vals)
            :else (vec resume-vals)))
        ;; First time - actually yield
        (let [interp-ns (find-ns 'clua.interpreter.core)
              throw-yield (ns-resolve interp-ns 'throw-yield)]
          ;; Throw yield exception (will be caught by the stack machine)
          ;; Convert lazy seq to vector for proper handling
          (throw-yield (vec values) env/*current-env*))))
    ;; Not in a coroutine - error
    (throw (ex-info "coroutine.yield: cannot yield outside a coroutine"
                    {:type :yield-error}))))

(defn coroutine-status
  "Get the status of a coroutine.

   Usage: coroutine.status(co)
   Returns: \"suspended\", \"running\", \"normal\", or \"dead\""
  [coro]
  (when-not (and (map? coro) (= :lua-coroutine (:type coro)))
    (throw (ex-info "coroutine.status: argument must be a coroutine"
                    {:type :type-error})))

  (let [state @(:state coro)]
    (name (:status state))))

(defn coroutine-running
  "Return the running coroutine and whether it's the main thread.

   Usage: coroutine.running()
   Returns: current-coroutine, false if in coroutine
            main-thread, true if in main thread"
  []
  (if-let [coro (coro/get-current-coroutine)]
    [coro false]
    [coro/main-thread true]))

(defn coroutine-wrap
  "Create a wrapped coroutine that can be called like a function.

   Usage: local f = coroutine.wrap(fn)
            f(...)  -- resumes the coroutine

   Returns: wrapper function"
  [func]
  (let [coro (coroutine-create func)]
    (fn [& args]
      (let [[success & results] (apply coroutine-resume coro args)]
        (if success
          ;; Return values — empty results means coroutine returned no values.
          ;; Return [] (empty vector) so callers in multi-value last-arg position
          ;; (e.g. table.pack(co())) see 0 values rather than a single nil.
          (cond
            (empty? results) []
            (= 1 (count results)) (first results)
            :else (vec results))
          ;; Error - throw it
          ;; Preserve the original Lua error value in :lua-error so pcall can recover it
          (let [err-val (first results)
                err-msg (cond
                          (string? err-val) err-val
                          (nil? err-val) "coroutine error: nil"
                          (and (map? err-val) (= :lua-function (:type err-val)))
                          (str "coroutine error: function:" (Integer/toHexString (System/identityHashCode err-val)))
                          (and (map? err-val) (= :lua-coroutine (:type err-val)))
                          (str "coroutine error: thread:" (Integer/toHexString (System/identityHashCode err-val)))
                          :else (str "coroutine error: " err-val))]
            (throw (ex-info err-msg
                            {:type :coroutine-error :lua-error err-val}))))))))

(defn coroutine-isyieldable
  "Check if a coroutine can yield.

   Usage: coroutine.isyieldable([co])
   - No argument: true if the running coroutine can yield (not main thread,
     not inside a non-yieldable native callback).
   - With co: true if coroutine co is yieldable (not the main thread, and
     not dead)."
  ([] (coro/is-yieldable?))
  ([co]
   (if (:main-thread co)
     false
     (let [state @(:state co)]
       (not= :dead (:status state))))))

(defn coroutine-close
  "Close a coroutine, putting it in a dead state.

   Usage: coroutine.close()   — close the currently running coroutine (self-close)
          coroutine.close(co) — force-close a suspended coroutine
   Returns: true, nil  — success (normal dead or force-closed suspended)
            false, err — coroutine died with an error (first call only)

   For suspended coroutines, runs all pending __close metamethods (to-be-closed
   variables in scope at the point of suspension) in LIFO scope order before
   marking the coroutine dead.

   Self-close (no args) throws a :self-close signal that propagates through the
   stack machine, running __close callbacks, then terminates the coroutine."
  ([]
   (when-not (coro/in-coroutine?)
     (throw (ex-info "attempt to close main thread" {:type :error})))
   (throw (ex-info "self-close" {:type :self-close})))
  ([co]
   (when-not (and (map? co) (= :lua-coroutine (:type co)))
     (throw (ex-info "bad argument #1 to 'close' (coroutine expected)" {:type :error})))
   (let [state-atom (:state co)
         coro-state @state-atom]
     (case (:status coro-state)
       :running (if (:main-thread co)
                  (throw (ex-info "cannot close main thread" {:type :error}))
                  (throw (ex-info "cannot close running coroutine" {:type :error})))
       :normal (throw (ex-info "cannot close normal coroutine" {:type :error}))
       :dead (if (contains? coro-state :lua-error)
               (let [err-val (:lua-error coro-state)]
                 (swap! state-atom dissoc :lua-error)
                 [false err-val])
               [true nil])
       :suspended
       (let [expr-stack (:expr-stack coro-state)
             sm-ns (find-ns 'clua.interpreter.stack-machine)
             run-close-list! (ns-resolve sm-ns 'run-close-list!)
             ;; Collect block frames with non-empty close-lists, innermost first.
             ;; expr-stack is ordered outermost (index 0) to innermost (last).
             close-frames (when (and run-close-list! expr-stack)
                            (filter #(and (= :block (:type %)) (seq (:close-list %)))
                                    (reverse expr-stack)))
             ;; Find an env with a call-stack atom for debug.getinfo inside __close.
             coro-env (when expr-stack
                        (some #(when (= :block (:type %)) (:env %)) expr-stack))
             ;; Run all close-lists, threading errors from inner to outer scope.
             ;; Initial error is nil (forced close, not an error).
             final-err (when (seq close-frames)
                         (reduce (fn [err frame]
                                   (run-close-list! (:close-list frame)
                                                    (or coro-env (:env frame))
                                                    err))
                                 nil
                                 close-frames))]
         (reset! state-atom (assoc coro-state :status :dead :call-stack []))
         (if final-err
           (let [extract-err (ns-resolve sm-ns 'extract-lua-error)]
             [false (if extract-err (extract-err final-err) (ex-message final-err))])
           [true nil]))))))

(defn coroutine-get-resume-value
  "Internal function to get the value passed to the last resume.
   This is used by the CPS transformation to capture resume values.

   Usage: coroutine.__get_resume_value()
   Returns: the first value passed to resume, or nil"
  []
  (if-let [current-coro (coro/get-current-coroutine)]
    (let [coro-state @(:state current-coro)
          resume-vals (:resume-values coro-state)]
      (cond
        (nil? resume-vals) nil
        (and (seqable? resume-vals) (empty? resume-vals)) nil
        (and (seqable? resume-vals) (>= (count resume-vals) 1)) (first resume-vals)
        :else resume-vals))
    nil))

(def coroutine-lib
  "The complete coroutine library for Lua."
  {"create" coroutine-create
   "resume" coroutine-resume
   "yield" coroutine-yield
   "status" coroutine-status
   "running" coroutine-running
   "wrap" coroutine-wrap
   "isyieldable" coroutine-isyieldable
   "close" coroutine-close
   ;; Internal function for CPS transformation
   "__get_resume_value" coroutine-get-resume-value})
