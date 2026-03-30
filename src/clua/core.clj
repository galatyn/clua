(ns clua.core
  "CLua - A sandboxed Lua 5.5 interpreter written in Clojure.

   Core library API for parsing and executing Lua code safely.

   Target Lua version: 5.5
   Reference: https://www.lua.org/manual/5.5/

   This is the main namespace to require when using clua as a library."
  (:require [clua.interpreter.convert :as convert]
            [clua.interpreter.env :as env]
            [clua.interpreter.api :as interp]
            [clua.parser.parser :as parser]
            [clua.stdlib.core :as stdlib])
  (:import (clojure.lang ExceptionInfo)))
(set! *warn-on-reflection* true)


;; ============================================================================
;; Records
;; ============================================================================

(defrecord CompiledScript [ast source])

(defrecord LuaState [lua-env owner])


(defn wrap-fn
  "Wraps a single Clojure function for transparent use in Lua.

   The wrapper automatically converts:
   - Lua arguments → Clojure values before calling the function
     (lua-tables become maps with keyword keys and 1-based integer keys)
   - Clojure return value → Lua value after the function returns
     (maps become lua-tables, vectors become 1-based lua-tables)

   Example:
     (clua/execute (stdlib/sandbox-standard)
       {:globals {:http_get  (clua/wrap-fn (fn [url] {:status 200 :body \"ok\"}))
                  :http_post (clua/wrap-fn (fn [url body] {:status 201}))}}
       lua-script)"
  [f]
  (fn [& args]
    (let [clj-args (map #(convert/lua->clj %) args)
          result (apply f clj-args)]
      (convert/clj->lua result))))

;; ============================================================================
;; Private helpers
;; ============================================================================

(defn- sanitize-stack-frame
  "Strip circular/unbounded fields from a stack-trace frame, keeping only
   safe, serializable data."
  [frame]
  (select-keys frame [:name :namewhat :line :column :extraargs :istailcall]))

(defn- build-exit-result
  "Build a result map for a script that called os.exit(code).
   Exit code 0 (or true) is considered success; any other code is failure."
  [^ExceptionInfo e]
  (let [code (:code (ex-data e))]
    {:ok (zero? (long code)) :exit-code code}))

(defn- build-error-result
  "Build a safe, serializable error result from an ExceptionInfo.
   Extracts useful fields from ex-data and sanitizes the stack trace.
   Never includes raw :data (which may contain circular env references)."
  [^ExceptionInfo e]
  (let [data (ex-data e)]
    (cond-> {:ok false
             :error (ex-message e)
             :line (or (:line data) (:error-line data))
             :column (:column data)}
      (:type data) (assoc :type (:type data))
      (:stack-trace data) (assoc :stack-trace (mapv sanitize-stack-frame (:stack-trace data))))))

(defn- build-lua-env
  "Build a Lua execution environment from the given options.
   source may be nil (e.g. when building a state before the script is known).
   When output-fn is provided, lua-print is injected into the sandbox so that
   Lua print() calls route through *output-fn* (backward-compatible behaviour)."
  [source sandbox globals step-limit memory-limit chunk-name output-fn warn-fn]
  (let [base-globals (or sandbox (stdlib/sandbox-standard))
        base-globals (cond-> base-globals
                       output-fn (assoc "print" stdlib/lua-print)
                       warn-fn   (assoc "warn" stdlib/lua-warn))
        converted-globals (into {} (map (fn [[k v]]
                                         (if (and (keyword? k) (= "fn" (namespace k)))
                                           [(name k) (wrap-fn v)]
                                           [(name k) (convert/clj->lua v)]))
                                       globals))
        all-globals (merge base-globals converted-globals)]
    (cond-> (-> (env/make-env all-globals)
                (env/with-step-limit step-limit)
                (env/with-memory-limit memory-limit))
      source (env/with-source source)
      chunk-name (env/with-chunk-name chunk-name))))

(defn- run-compiled
  "Execute an already-parsed AST in the given environment."
  [ast lua-env output-fn warn-fn key-fn]
  (let [raw-result (binding [stdlib/*output-fn* output-fn
                             stdlib/*warn-fn*   warn-fn]
                     (interp/eval-chunk ast lua-env))]
    (if (false? key-fn)
      raw-result
      (convert/lua->clj raw-result key-fn))))

(defn- prepare-env-for-run!
  "Reset per-run execution state in an existing lua-env and return an updated env
   with the new source/chunk-name. Atom resets are in-place mutations.
   source may be nil (e.g. for call-fn where there is no new source)."
  [lua-env source chunk-name]
  (reset! (:current-line lua-env) nil)
  (reset! (:current-column lua-env) nil)
  (reset! (:current-stmt-index lua-env) nil)
  (reset! (:call-stack lua-env) [])
  (reset! (:env-redirect lua-env) nil)
  (env/reset-steps! lua-env)
  (env/reset-memory! lua-env)
  (cond-> lua-env
    source (env/with-source source)
    chunk-name (env/with-chunk-name chunk-name)))


;; ============================================================================
;; Thread-ownership guard
;; ============================================================================

(defn- acquire-state!
  "Atomically mark state as owned by the current thread.
   Throws if another thread is already executing with this state."
  [^LuaState state]
  (let [current (Thread/currentThread)]
    (when-not (compare-and-set! (:owner state) nil current)
      (let [owner @(:owner state)]
        (throw (ex-info
                (str "LuaState is already in use by thread \"" (.getName ^Thread owner)
                     "\". LuaState cannot be shared across threads.")
                {:type :concurrent-state-access
                 :owner-thread owner
                 :current-thread current}))))))

(defn- release-state!
  "Release the thread-ownership lock on state."
  [^LuaState state]
  (reset! (:owner state) nil))


;; ============================================================================
;; Public API — compile / state / run
;; ============================================================================

(defn parse
  "Compile Lua source into a reusable CompiledScript.
   The parse step happens once; the result can be passed to run multiple times
   without re-parsing.
   Returns CompiledScript on success, or {:ok false :error ...} on failure. Never throws."
  [source]
  (try
    (->CompiledScript (parser/parse-and-transform source) source)
    (catch ExceptionInfo e
      (build-error-result e))
    (catch Exception e
      {:ok false :error (ex-message e)})))

(defn- to-compiled-script
  "Ensure code is a CompiledScript — parse it if it's a string."
  [code]
  (if (instance? CompiledScript code) code (parse code)))

(defn- execute-compiled
  "Run a CompiledScript in a fresh stateless environment. Never throws."
  [cs sandbox opts]
  (let [globals      (get opts :globals {})
        step-limit   (get opts :step-limit 1000000)
        memory-limit (get opts :memory-limit env/default-memory-limit)
        output-fn    (get opts :output-fn nil)
        warn-fn      (get opts :warn-fn nil)
        key-fn       (get opts :key-fn keyword)
        chunk-name   (get opts :chunk-name nil)
        lua-env      (build-lua-env (:source cs) sandbox globals step-limit memory-limit chunk-name output-fn warn-fn)]
    (try
      {:ok true :result (run-compiled (:ast cs) lua-env output-fn warn-fn key-fn)}
      (catch ExceptionInfo e
        (if (= :exit (:type (ex-data e)))
          (build-exit-result e)
          (build-error-result e)))
      (catch Exception e
        {:ok false
         :error  (ex-message e)
         :line   (when-let [a (:current-line lua-env)] @a)
         :column (when-let [a (:current-column lua-env)] @a)}))))

(defn- execute-compiled-unsafe
  "Run a CompiledScript in a fresh stateless environment. Throws on error."
  [cs sandbox opts]
  (let [globals      (get opts :globals {})
        step-limit   (get opts :step-limit 1000000)
        memory-limit (get opts :memory-limit env/default-memory-limit)
        output-fn    (get opts :output-fn nil)
        warn-fn      (get opts :warn-fn nil)
        key-fn       (get opts :key-fn keyword)
        chunk-name   (get opts :chunk-name nil)
        lua-env      (build-lua-env (:source cs) sandbox globals step-limit memory-limit chunk-name output-fn warn-fn)]
    (run-compiled (:ast cs) lua-env output-fn warn-fn key-fn)))

(defn make-state
  "Create a LuaState with persistent globals, reusable across run calls.

   Arities:
   - (make-state)              — sandbox-standard, no options
   - (make-state sandbox)      — explicit sandbox, no options
   - (make-state sandbox opts) — sandbox + options map

   Options map keys:
   - :globals      - Initial global variables (map of keyword/string -> value)
   - :step-limit   - Maximum execution steps per run (default 1000000)
   - :memory-limit - Maximum memory allocation in bytes (default 10MB)

   The returned LuaState is NOT thread-safe for concurrent runs."
  ([]
   (make-state (stdlib/sandbox-standard) {}))
  ([sandbox]
   (make-state sandbox {}))
  ([sandbox opts]
   (let [globals      (get opts :globals {})
         step-limit   (get opts :step-limit 1000000)
         memory-limit (get opts :memory-limit env/default-memory-limit)]
     (->LuaState (build-lua-env nil sandbox globals step-limit memory-limit nil nil nil) (atom nil)))))

(defn run-unsafe
  "Run Lua code against a LuaState. Throws on error. Returns the result value directly.

   Globals accumulated by previous calls are preserved.
   Per-call state (steps, memory, position, call-stack) is reset before each run.

   Arities:
   - (run-unsafe state code)
   - (run-unsafe state opts code)

   state - LuaState created with make-state
   opts  - optional map:
     :step-limit   — override step limit for this run
     :memory-limit — override memory limit for this run
     :output-fn    — print output handler
     :key-fn       — result key conversion (default: keyword; false = raw Lua values)
     :chunk-name   — chunk name for error messages
   code  - Lua source string or CompiledScript from parse"
  ([^LuaState state code]
   (run-unsafe state {} code))
  ([^LuaState state opts code]
   (let [cs (to-compiled-script code)]
     (when-not (instance? CompiledScript cs)
       (throw (ex-info (:error cs) cs)))
     (acquire-state! state)
     (try
       (let [step-limit   (get opts :step-limit 1000000)
             memory-limit (get opts :memory-limit env/default-memory-limit)
             output-fn    (get opts :output-fn nil)
             warn-fn      (get opts :warn-fn nil)
             key-fn       (get opts :key-fn keyword)
             chunk-name   (get opts :chunk-name nil)
             lua-env      (cond-> (prepare-env-for-run! (:lua-env state) (:source cs) chunk-name)
                            step-limit   (assoc :step-limit step-limit)
                            memory-limit (assoc :memory-limit memory-limit))]
         (run-compiled (:ast cs) lua-env output-fn warn-fn key-fn))
       (finally
         (release-state! state))))))

(defn run
  "Run Lua code against a LuaState. Never throws.

   Globals accumulated by previous calls are preserved.
   Per-call state (steps, memory, position, call-stack) is reset before each run.

   Arities:
   - (run state code)
   - (run state opts code)

   state - LuaState created with make-state
   opts  - optional map:
     :step-limit   — override step limit for this run
     :memory-limit — override memory limit for this run
     :output-fn    — print output handler
     :key-fn       — result key conversion (default: keyword; false = raw Lua values)
     :chunk-name   — chunk name for error messages
   code  - Lua source string or CompiledScript from parse

   Returns {:ok true :result <value>} or {:ok false :error <msg> :line <n> ...}."
  ([^LuaState state code]
   (run state {} code))
  ([^LuaState state opts code]
   (let [cs (to-compiled-script code)]
     (if (instance? CompiledScript cs)
       (do
         (acquire-state! state)
         (try
           (let [step-limit   (get opts :step-limit 1000000)
                 memory-limit (get opts :memory-limit env/default-memory-limit)
                 output-fn    (get opts :output-fn nil)
                 warn-fn      (get opts :warn-fn nil)
                 key-fn       (get opts :key-fn keyword)
                 chunk-name   (get opts :chunk-name nil)
                 lua-env      (cond-> (prepare-env-for-run! (:lua-env state) (:source cs) chunk-name)
                                step-limit   (assoc :step-limit step-limit)
                                memory-limit (assoc :memory-limit memory-limit))]
             (try
               {:ok true :result (run-compiled (:ast cs) lua-env output-fn warn-fn key-fn)}
               (catch ExceptionInfo e
                 (if (= :exit (:type (ex-data e)))
                   (build-exit-result e)
                   (build-error-result e)))
               (catch Exception e
                 {:ok false
                  :error  (ex-message e)
                  :line   (when-let [a (:current-line lua-env)] @a)
                  :column (when-let [a (:current-column lua-env)] @a)})))
           (finally
             (release-state! state))))
       cs))))


(defn- call-fn-core
  "Execute a Lua function looked up by name in lua-env's globals."
  [lua-env fn-name args output-fn warn-fn key-fn]
  (let [fn-value (binding [env/*global-scope* (:global-scope lua-env)]
                   (env/lookup lua-env fn-name))
        converted-args (mapv convert/clj->lua args)
        raw-result (binding [stdlib/*output-fn* output-fn
                             stdlib/*warn-fn*   warn-fn
                             env/*current-env* lua-env
                             env/*global-scope* (:global-scope lua-env)]
                     (interp/call-function fn-value converted-args lua-env))]
    (if (false? key-fn)
      raw-result
      (convert/lua->clj raw-result key-fn))))

(defn call-fn
  "Look up a named function in state's globals and call it.

   state   - LuaState previously populated by one or more run calls
   fn-name - name of the global Lua function to call (string)
   args    - vector of Clojure values passed as arguments (auto-converted to Lua)
   opts    - optional map:
     :output-fn    — print output handler
     :key-fn       — result key conversion (default: keyword; false = raw Lua values)
     :step-limit   — override step limit for this call
     :memory-limit — override memory limit for this call

   Per-call state (steps, memory, position, call-stack) is reset before each call.
   Globals accumulated by previous run or call-fn calls are preserved.

   Returns {:ok true :result <value>} or {:ok false :error <msg> :line <n> ...}."
  ([state fn-name args]
   (call-fn state fn-name args {}))
  ([state fn-name args opts]
   (let [output-fn    (get opts :output-fn nil)
         warn-fn      (get opts :warn-fn nil)
         key-fn       (get opts :key-fn keyword)
         step-limit   (get opts :step-limit 1000000)
         memory-limit (get opts :memory-limit env/default-memory-limit)]
     (acquire-state! state)
     (try
       (let [lua-env (cond-> (prepare-env-for-run! (:lua-env state) nil nil)
                       step-limit   (assoc :step-limit step-limit)
                       memory-limit (assoc :memory-limit memory-limit))]
         (try
           {:ok true :result (call-fn-core lua-env fn-name args output-fn warn-fn key-fn)}
           (catch ExceptionInfo e
             (if (= :exit (:type (ex-data e)))
               (build-exit-result e)
               (build-error-result e)))
           (catch Exception e
             {:ok false
              :error (ex-message e)
              :line (when-let [a (:current-line lua-env)] @a)
              :column (when-let [a (:current-column lua-env)] @a)})))
       (finally
         (release-state! state))))))


;; ============================================================================
;; Public API — stateless execute
;; ============================================================================

(defn execute
  "Execute Lua code in a fresh sandboxed environment. Never throws.

   Each call builds an independent environment — safe to call concurrently
   from any number of threads. For persistent globals across calls use
   make-state + run instead.

   Arities:
   - (execute source)              — sandbox-standard, no options
   - (execute sandbox source)      — explicit sandbox, no options
   - (execute sandbox opts source) — sandbox + options map + source

   source may be a Lua string or a CompiledScript from parse (parse-once,
   execute-many without re-parsing).

   Sandbox levels:
   - (sandbox-minimal)  - No libraries, no print (maximum security)
   - (sandbox-standard) - All libraries, no print (DEFAULT - safe for untrusted)
   - (sandbox-full)     - All libraries + print (for trusted/development)

   Options map keys:
   - :globals      - Additional global variables (map of keyword/string -> value;
                     Clojure maps/vectors are auto-converted to Lua tables)
   - :step-limit   - Maximum execution steps (default 1000000)
   - :memory-limit - Maximum memory allocation in bytes (default 10MB)
   - :output-fn    - Print output handler (injects print into sandbox)
   - :warn-fn      - Warning output handler (injects warn into sandbox)
   - :key-fn       - Key conversion for result tables (default: keyword;
                     pass false to skip conversion and return raw Lua values)
   - :chunk-name   - Chunk name for error messages

   See also: execute-unsafe, parse, make-state, run.

   Returns {:ok true :result <value>} on success,
   or {:ok false :error <message> :line <n> :column <n> :stack-trace [...]} on failure."
  ([source]
   (execute (stdlib/sandbox-standard) {} source))
  ([sandbox source]
   (execute sandbox {} source))
  ([sandbox opts source]
   (let [cs (to-compiled-script source)]
     (if (instance? CompiledScript cs)
       (execute-compiled cs sandbox opts)
       cs))))

(defn execute-unsafe
  "Execute Lua code in a fresh sandboxed environment. Throws on error.
   Returns the result value directly (not wrapped in a map).

   Same arities and options as execute. Use when you are confident the
   script will succeed and want to skip the result-map unwrapping.

   See execute for full documentation."
  ([source]
   (execute-unsafe (stdlib/sandbox-standard) {} source))
  ([sandbox source]
   (execute-unsafe sandbox {} source))
  ([sandbox opts source]
   (let [cs (to-compiled-script source)]
     (if (instance? CompiledScript cs)
       (execute-compiled-unsafe cs sandbox opts)
       (throw (ex-info (:error cs) cs))))))
