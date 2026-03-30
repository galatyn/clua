(ns clua.interpreter.core
  "Function calls, block evaluation, and top-level entry point for the Lua interpreter."
  (:require [clua.interpreter.coro-runtime :as coro]
            [clua.interpreter.env :as env]
            [clua.interpreter.expressions :as expr]
            [clua.interpreter.stack-machine :as stack-machine]
            [clua.interpreter.tables :as tables]
            [clua.interpreter.types :as types])
  (:import (clojure.lang ArityException)))
(set! *warn-on-reflection* true)


;;; Dynamic vars for tail recursion tracking and error reporting

(def ^:dynamic *current-function-name* nil)
(def ^:dynamic *current-function* nil)                      ; The actual function object being executed

;; Forward declarations for mutual recursion
(declare eval-block call-function)

(defn call-function
  "Call a function (native or Lua) with arguments."
  [target arg-values env]
  (cond
    ;; Multi-value return used as callee - extract first value (Lua semantics)
    (vector? target)
    (call-function (first target) arg-values env)

    ;; Native Clojure function
    (fn? target)
    (binding [env/*current-env* env]
      (try
        (expr/maybe-convert-result (apply target arg-values) env)
        (catch ArityException e
          ;; Lua silently ignores extra arguments; retry with fewer args
          (let [n (count arg-values)
                msg (.getMessage e)]
            (if (and (> n 0) (.contains msg (str "(" n ")")))
              ;; Extra args: recursively try with fewer args (can't use recur in catch)
              ((fn drop-extra [args]
                 (if (empty? args)
                   (throw (ex-info msg {:type :error}))
                   (try
                     (expr/maybe-convert-result (apply target args) env)
                     (catch ArityException _
                       (drop-extra (vec (butlast args)))))))
               (vec (butlast arg-values)))
              ;; Internal ArityException - convert to Lua error
              (throw (ex-info msg {:type :error})))))))

    ;; Lua function - always run via stack machine (handles TCO and yields)
    (= :lua-function (:type target))
    (let [outer-scope-count (count (:scopes (:env target)))
          base-env (-> (env/push-scope (:env target))
                       (assoc :outer-scope-count outer-scope-count))
          fn-joins (env/get-upvalue-joins target)
          func-env (if fn-joins (assoc base-env :upvalue-joins fn-joins) base-env)
          params (:params target)
          has-varargs (:varargs target)
          vararg-name (:vararg-name target)
          num-params (count params)
          _ (doseq [[param-name arg-val] (map vector params (concat arg-values (repeat nil)))]
              (env/define! func-env param-name arg-val))
          _ (when has-varargs
              (let [varargs (vec (drop num-params arg-values))]
                (if vararg-name
                  ;; Lua 5.5 named vararg: create table t = table.pack(...) and make
                  ;; "..." a live reference to it so mutations of t are reflected in ...
                  (let [vt (tables/make-table)]
                    (tables/table-set! vt "n" (count varargs))
                    (dorun (map-indexed (fn [i v] (tables/table-set! vt (unchecked-inc (long i)) v)) varargs))
                    (env/define! func-env vararg-name vt)
                    (env/define! func-env "..." {:vararg-table vt}))
                  (env/define! func-env "..." varargs))))
          stmts (:statements (:body target))
          block-frame (stack-machine/make-function-block-frame stmts func-env)
          run-result (binding [env/*current-env* func-env
                               *current-function-name* (:name target)
                               *current-function* target]
                       (stack-machine/run-stack-machine [block-frame] func-env))
          v (:value run-result)]
      (case (:type run-result)
        :done
        (cond
          (and (vector? v) (> (count v) 1)) v
          (and (vector? v) (= (count v) 1)) (first v)
          :else v)
        :yield
        ;; Save the inner stack machine state in the coroutine's state-atom so that
        ;; a native function (e.g. dofile) wrapping this Lua function call can be
        ;; resumed — the state-atom is retrieved via :pending-inner-stack.
        (do (when-let [coro (coro/get-current-coroutine)]
              (swap! (:state coro) assoc :pending-inner-stack (:stack run-result)))
            (throw (ex-info "yield" {:type :coro-yield :values (:values run-result)})))
        :error
        (let [err-ex (:error run-result)
              data (ex-data err-ex)
              line (or (:line data) (:error-line data))
              msg (ex-message err-ex)
              located (if (and line (not (:line data)))
                        (str "line " line ": " msg)
                        msg)
              ;; Capture whether we're in a non-yieldable context (e.g. string.gsub
              ;; callback, sort comparator) before any surrounding binding unwinds it.
              ;; recover-from-pcall uses this to decide whether __close can yield.
              unyieldable? (pos? (long coro/*unyieldable-depth*))
              updated-data (if unyieldable?
                             (assoc data :line line :unyieldable-context true)
                             (assoc data :line line))]
          (throw (ex-info located updated-data)))))

    ;; Callable table via __call metamethod
    (types/lua-table? target)
    (if-let [call-mm (tables/get-metamethod target "__call")]
      (call-function call-mm (cons target arg-values) env)
      (let [[line col stmt-idx] (env/get-position env)
            stack-trace (env/get-stack-trace env)]
        (throw (ex-info (str "attempt to call a " (tables/lua-type-name target) " value")
                        {:type :call-error
                         :line line
                         :column col
                         :statement-index stmt-idx
                         :stack-trace stack-trace
                         :value target}))))

    :else
    (let [[line col stmt-idx] (env/get-position env)
          stack-trace (env/get-stack-trace env)]
      (throw (ex-info (str "attempt to call a " (tables/lua-type-name target) " value")
                      {:type :call-error
                       :line line
                       :column col
                       :statement-index stmt-idx
                       :stack-trace stack-trace
                       :value target})))))

;;; Block evaluation

(defn throw-yield
  "Throw a yield exception with only values.

   IMPORTANT: Exception only contains :values to avoid circular references.
   Full yield state (:env, :locals, :pc, :call-stack) will be captured by the handler
   and stored in the coroutine atom, NOT in the exception."
  [values _env]
  (throw (ex-info "yield"
                  {:type :coro-yield
                   :values values})))


;;; Top-level evaluation

(defn eval-chunk
  "Evaluate a top-level chunk (program)."
  [ast env]
  (env/reset-steps! env)
  ;; Push a main-chunk frame so that debug.getlocal/getinfo level counting
  ;; matches PUC-Lua: the main chunk is a vararg Lua function at the bottom
  ;; of the call stack.  This also ensures that tail-call-optimised returns
  ;; (e.g. `return debug.getlocal(1,-1)`) still find a valid frame at level 1.
  (let [main-fn {:type :lua-function :params [] :varargs true :body nil :is-main-chunk true}
        ;; env-atom tracks live env so debug.getlocal(level=main-chunk) works inside loops
        env-atom (atom env)]
    (env/push-stack-frame! env "main chunk" 0 0 main-fn env-atom)
    (try
      (binding [env/*current-env* env
                env/*global-scope* (:global-scope env)]     ; Bind global scope for access during execution
        (let [body (if (= :chunk (:type ast))
                     (first (:body ast))
                     ast)
              ;; Run via stack machine (handles both coroutine and non-coroutine contexts)
              stmts (:statements body)
              block-frame (assoc (stack-machine/make-block-frame stmts env)
                            :frame-env-atom env-atom)
              run-result (stack-machine/run-stack-machine [block-frame] env)
              v (:value run-result)]
          (case (:type run-result)
            :done
            (cond
              (and (vector? v) (> (count v) 1)) v
              (and (vector? v) (= (count v) 1)) (first v)
              :else v)
            :yield
            (let [coro-state (coro/get-current-coroutine)]
              (when coro-state
                (swap! (:state coro-state) assoc :expr-stack (:stack run-result)))
              (throw (ex-info "yield" {:type :coro-yield :values (:values run-result)})))
            :error
            (throw (:error run-result)))))
      (finally
        (env/pop-stack-frame! env)))))

;; Wire up forward declarations in other modules
(alter-var-root #'tables/call-function (constantly call-function))
(alter-var-root #'expr/call-function (constantly call-function))

;; Wire up stack machine
(alter-var-root #'stack-machine/*call-function* (constantly call-function))
