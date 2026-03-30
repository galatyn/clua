(ns clua.interpreter.env
  "Environment management for sandboxed Lua execution.

   Environments are stacks of scopes (maps). Variable lookup
   walks up the stack, assignment modifies the appropriate scope."
  (:require [clojure.string :as str]
            [clua.stdlib.xoshiro256 :as xoshiro]
            [clua.debug.trace-macro :as trace])
  (:import (java.text DecimalFormatSymbols)
           (java.util ArrayList HashMap LinkedHashMap Locale Map)))

(set! *warn-on-reflection* true)

;; Dynamic var for current execution environment
;; Used by stdlib functions that need to track memory allocations
(def ^:dynamic *current-env* nil)

;; Dynamic var for global scope (HashMap)
;; Avoids circular references by not storing global scope in :scopes or function :env
(def ^:dynamic *global-scope* nil)

;; Dynamic var set to true when a native function is being called via method syntax (:).
;; Used by string functions to distinguish 'bad argument #1' from 'bad argument #2'
;; (since method calls shift the user-visible argument number by -1).
(def ^:dynamic *in-method-call* false)

;; Registry for env-tables used by load() to avoid circular references
;; Maps env-table-id (UUID) -> actual Lua table
(def ^:private env-table-registry (atom {}))

;; Registry for debug.upvaluejoin redirects.
;; Maps Lua function identity -> Clojure map of
;;   {[scope-identity-hash varname] -> [target-scope target-varname]}
;; Uses IdentityHashMap so distinct function objects with equal content get
;; separate entries (matches Lua upvalue-cell identity semantics).
(def ^:private ^Map upvalue-join-registry
  (java.util.Collections/synchronizedMap (java.util.IdentityHashMap.)))

;; Special marker value placed in local scopes by 'global X' declarations
;; to indicate that lookups/assignments should bypass the local scopes
;; and hit the global environment.
(def ^:const global-ref-marker ::global-ref)

(defn get-upvalue-joins
  "Return the upvalue-join map for a Lua function, or nil if none registered."
  [lua-fn]
  (.get upvalue-join-registry lua-fn))

(defn register-upvalue-join!
  "Register a redirect: when lua-fn reads/writes (scope1, name1) redirect it
   to (scope2, name2) instead. Called by debug.upvaluejoin."
  [lua-fn ^HashMap scope1 name1 ^HashMap scope2 name2]
  (let [key [(System/identityHashCode scope1) name1]
        existing (.get upvalue-join-registry lua-fn)
        new-map (assoc (or existing {}) key [scope2 name2])]
    (.put upvalue-join-registry lua-fn new-map)))

(defn register-env-table!
  "Register an env-table and return its ID."
  [env-table]
  (let [id (java.util.UUID/randomUUID)]
    (swap! env-table-registry assoc id env-table)
    id))

(defn resolve-env-table
  "Resolve an env-table from its ID, or return nil if not found."
  [id]
  (get @env-table-registry id))

;; Forward declarations for position and stack tracking
(declare get-position)
(declare get-stack-trace)

;; Table access for env-table (uses delayed resolution to avoid circular dependency)
(def ^:private cached-table-get-fn
  (delay @(ns-resolve (the-ns 'clua.interpreter.tables) 'table-get-with-meta)))

(def ^:private cached-table-set!-fn
  (delay @(ns-resolve (the-ns 'clua.interpreter.tables) 'table-set-with-meta!)))

(defn- env-table-get
  "Get a value from a Lua table used as env-table (respects __index metamethod)"
  [table key env]
  (trace/traced "env-table-get" key
                (@cached-table-get-fn table key env)))

(defn- env-table-set!
  "Set a value in a Lua table used as env-table (respects __newindex metamethod)"
  [table key value env]
  (trace/traced "env-table-set!" key value
                (@cached-table-set!-fn table key value env)))

(def ^:const default-memory-limit
  "Default memory limit: 10 MB"
  10485760)

(declare make-global-table)

(defn make-env
  "Create a new environment with optional global bindings.

   Global scope is stored separately from :scopes to avoid circular references.
   :scopes contains only LOCAL scopes. Global scope is accessed via *global-scope* dynamic var."
  ([] (make-env {}))
  ([globals]
   ;; Use Java HashMap for global scope
   (let [global-scope (HashMap.)]
     (doseq [[k v] globals]
       (.put global-scope k v))
     (let [g-table (make-global-table global-scope)]
       {:global-scope global-scope                          ; Stored separately, not in :scopes
        :g-table g-table                                    ; Cached _G/_ENV table (same object for identity)
        :env-redirect (atom nil)                            ; _ENV redirect: set when chunk does _ENV = val
        :scopes []                                          ; Only local scopes, no global
        :step-count (long-array [0])                        ; Changed from atom to mutable long array
        :step-limit 1000000
        :memory-used (long-array [0])                       ; Changed from atom to mutable long array
        :memory-limit default-memory-limit
        :rng (xoshiro/make-state (System/currentTimeMillis) 0) ; xoshiro256** state
        :source nil
        :chunk-name nil
        :source-lines nil
        :current-line (atom nil)
        :current-column (atom nil)
        :current-stmt-index (atom nil)
        :call-stack (atom [])
        :hook (atom nil)
        :locale-numeric (atom {:java-locale Locale/ROOT :name "C"})
        :type-metatables (atom {})}))))

(defn push-scope
  "Push a new local scope onto the environment.
   Uses LinkedHashMap to preserve insertion order for debug.getlocal enumeration."
  [env]
  (update env :scopes conj (LinkedHashMap.)))

(defn- make-global-table
  "Create a Lua table backed by a global scope map for _G/_ENV access.
   The table's :data IS global-scope, so reads/writes go directly to global scope.
   Uses *global-scope* dynamic var if no scope argument provided."
  ([] (make-global-table *global-scope*))
  ([^HashMap global-scope]
   (let [g-table {:type :lua-table
                  :data global-scope
                  :array (ArrayList.)
                  :metatable (object-array [nil])}
         meta-data (HashMap.)
         meta-table {:type :lua-table
                     :data meta-data
                     :array (ArrayList.)
                     :metatable (object-array [nil])}]
     ;; __index handles the _G._G self-reference
     (.put ^HashMap meta-data "__index"
           (fn [_table key]
             (if (= key "_G")
               g-table
               (.get global-scope key))))
     (aset ^objects (:metatable g-table) 0 meta-table)
     g-table)))

(defn lookup
  "Look up a variable in the environment, searching from local to global.

   Local scopes are in :scopes, global scope is accessed via *global-scope* dynamic var.
   If env-table is set (from load()), it overrides global scope lookups."
  [env name]
  (cond
    ;; _G - return cached global table (same object for identity checks)
    (= name "_G")
    (or (:g-table env) (when *global-scope* (make-global-table)))

    ;; _ENV - check env-redirect first, then env-table-id, then cached global table
    (= name "_ENV")
    (or (some-> (:env-redirect env) deref)
        (if-let [id (:env-table-id env)]
          (resolve-env-table id)
          (or (:g-table env) (when *global-scope* (make-global-table)))))

    ;; Normal lookup: check local scopes first, then global or env-table
    :else
    (let [env-table (when-let [id (:env-table-id env)] (resolve-env-table id))
          redirect (some-> (:env-redirect env) deref)
          reversed-scopes (rseq (:scopes env))
          joins (:upvalue-joins env)]
      (loop [scopes reversed-scopes]
        (if (seq scopes)
          (let [^HashMap scope (first scopes)]
            (if (.containsKey scope name)
              (let [val (if-let [[^HashMap ts tn]
                                 (when joins (get joins [(System/identityHashCode scope) name]))]
                          (.get ts tn)
                          (.get scope name))]
                (if (identical? val global-ref-marker)
                  (recur nil)
                  val))
              (recur (rest scopes))))
          ;; Not found in local scopes — check for local _ENV redirection
          (let [local-env (some (fn [^HashMap s]
                                  (when (.containsKey s "_ENV") (.get s "_ENV")))
                                reversed-scopes)]
            (cond
              local-env
              (env-table-get local-env name env)
              ;; _ENV was explicitly reassigned: redirect takes priority over env-table
              redirect
              (env-table-get redirect name env)
              (and env-table (map? env-table) (= :lua-table (:type env-table)))
              ;; env-table is the complete scope for load()ed chunks (no global fallback)
              (env-table-get env-table name env)
              :else
              (when *global-scope*
                (.get ^HashMap *global-scope* name)))))))))

(defn define!
  "Define a new variable in the current (top) scope.

   If there are local scopes, define in the topmost local scope.
   If no local scopes, define in global scope via *global-scope* dynamic var."
  [env name value]
  (if-let [^HashMap top-scope (peek (:scopes env))]
    ;; Have local scopes - define in topmost
    (.put top-scope name value)
    ;; No local scopes - define in global scope
    (when *global-scope*
      (.put ^HashMap *global-scope* name value)))
  value)

(defn undeclare!
  "Remove a variable from the innermost local scope that contains it.
   Used when a backward goto jumps out of a variable's declaration scope."
  [env name]
  (loop [scopes (rseq (vec (:scopes env)))]
    (when (seq scopes)
      (let [^LinkedHashMap scope (first scopes)]
        (if (.containsKey scope name)
          (.remove scope name)
          (recur (rest scopes)))))))

(defn assign!
  "Assign to an existing variable, or create in global scope if not found.

   Checks local scopes first, then assigns to global scope via *global-scope*.
   If env-table is set (from load()), it overrides global scope assignments."
  [env name value]
  (trace/traced "assign!" name value
                (let [env-table (when-let [id (:env-table-id env)] (resolve-env-table id))
                      redirect (some-> (:env-redirect env) deref)
                      reversed-scopes (rseq (:scopes env))]
                  (loop [scopes reversed-scopes]
                    (if (seq scopes)
                      (let [^HashMap scope (first scopes)]
                        (if (.containsKey scope name)
                          (let [joins (:upvalue-joins env)]
                            (if-let [[^HashMap ts tn]
                                     (when joins (get joins [(System/identityHashCode scope) name]))]
                              (let [current-val (.get ts tn)]
                                (if (identical? current-val global-ref-marker)
                                  (recur nil)
                                  (do (.put ts tn value) value)))
                              (let [current-val (.get scope name)]
                                (if (identical? current-val global-ref-marker)
                                  (recur nil)
                                  (do (.put scope name value) value)))))
                          (recur (rest scopes))))
                      ;; Not found in local scopes — determine where the write goes
                      (let [local-env (some (fn [^HashMap s]
                                              (when (.containsKey s "_ENV") (.get s "_ENV")))
                                            reversed-scopes)]
                        (cond
                          ;; _ENV assignment: update the redirect atom
                          (= name "_ENV")
                          (do (when-let [ra (:env-redirect env)] (reset! ra value)) value)
                          ;; local _ENV redirection
                          local-env
                          (env-table-set! local-env name value env)
                          ;; _ENV was explicitly reassigned: redirect takes priority over env-table
                          redirect
                          (env-table-set! redirect name value env)
                          ;; load() env-table (when no redirect)
                          env-table
                          (env-table-set! env-table name value env)
                          ;; Default: write to global scope
                          :else
                          (when *global-scope*
                            (if (nil? value)
                              (.remove ^HashMap *global-scope* name)
                              (.put ^HashMap *global-scope* name value))
                            value))))))))

(defn increment-steps!
  "Increment step counter and check against limit.
   Throws if limit exceeded (prevents infinite loops)."
  [env]
  (let [^longs step-array (:step-count env)
        ;; Direct array mutation - much faster than atom swap!
        count (let [current (aget step-array 0)
                    next-val (inc current)]
                (aset step-array 0 next-val)
                next-val)]
    (when (> count (long (:step-limit env)))
      (let [[line col stmt-idx] (get-position env)
            stack-trace (get-stack-trace env)]
        (throw (ex-info "Execution step limit exceeded"
                        {:type :step-limit-exceeded
                         :limit (:step-limit env)
                         :line line
                         :column col
                         :statement-index stmt-idx
                         :stack-trace stack-trace}))))))

(defn reset-steps!
  "Reset the step counter."
  [env]
  (aset ^longs (:step-count env) 0 (long 0)))

(defn with-step-limit
  "Return a new environment with the specified step limit."
  [env limit]
  (assoc env :step-limit limit))

(defn with-memory-limit
  "Return a new environment with the specified memory limit in bytes."
  [env limit]
  (assoc env :memory-limit limit))

(defn estimate-size
  "Estimate the memory size of a Lua value in bytes."
  [value]
  (cond
    (nil? value) 8
    (boolean? value) 8
    (number? value) 16
    (string? value) (+ 48 (* 2 (count value)))              ; Java String overhead + chars
    (and (map? value) (= :lua-table (:type value)))
    (+ 256                                                  ; Base table structure
       (* 64 (.size ^HashMap (:data value)))                ; HashMap size - no deref
       (* 24 (.size ^ArrayList (:array value))))            ; ArrayList size - no deref
    (and (map? value) (= :lua-function (:type value))) 128
    (fn? value) 64
    :else 32))

(defn track-allocation!
  "Track memory allocation and throw if limit exceeded.
   Returns the new total memory used."
  [env bytes]
  (when-let [^longs mem-array (:memory-used env)]
    ;; Direct array mutation - much faster than atom swap!
    (let [used (let [current (aget mem-array 0)
                     next-val (unchecked-add current (long bytes))]
                 (aset mem-array 0 next-val)
                 next-val)
          limit (long (:memory-limit env default-memory-limit))]
      (when (> used limit)
        (let [[line col stmt-idx] (get-position env)
              stack-trace (get-stack-trace env)]
          (throw (ex-info "Memory limit exceeded"
                          {:type :memory-limit-exceeded
                           :used used
                           :limit limit
                           :line line
                           :column col
                           :statement-index stmt-idx
                           :stack-trace stack-trace}))))
      used)))

(defn reset-memory!
  "Reset the memory counter."
  [env]
  (when-let [^longs mem-array (:memory-used env)]
    (aset mem-array 0 (long 0))))

;; ============================================================================
;; Source and position tracking
;; ============================================================================

(defn with-source
  "Return a new environment with source code stored for error reporting."
  [env source]
  (let [lines (str/split-lines source)]
    (assoc env
      :source source
      :source-lines (vec lines))))

(defn with-chunk-name
  "Return a new environment with an explicit chunk name for error messages.
   When set, overrides :source for error prefix formatting (e.g. '@errors.lua'
   produces 'errors.lua:N: ...' instead of '[string \"...\"]')."
  [env name]
  (assoc env :chunk-name name))

(defn set-position!
  "Set the current execution position (for error reporting)."
  ([env line column]
   (set-position! env line column nil))
  ([env line column stmt-index]
   (when-let [line-atom (:current-line env)]
     (reset! line-atom line))
   (when-let [col-atom (:current-column env)]
     (reset! col-atom column))
   (when-let [stmt-atom (:current-stmt-index env)]
     (reset! stmt-atom stmt-index))))

(defn get-position
  "Get the current execution position as [line column stmt-index].
   Line and column may be nil if only stmt-index is available."
  [env]
  (let [line (when-let [a (:current-line env)] @a)
        col (when-let [a (:current-column env)] @a)
        stmt-idx (when-let [a (:current-stmt-index env)] @a)]
    (when (or line stmt-idx)
      [line col stmt-idx])))

(defn get-source-line
  "Get a specific line from the source (1-indexed)."
  [env line-num]
  (when-let [lines (:source-lines env)]
    (let [n (long line-num)]
      (when (and (pos? n) (<= n (count lines)))
        (nth lines (unchecked-dec n))))))

;; ============================================================================
;; Call stack tracking for stack traces
;; ============================================================================

(defn push-stack-frame!
  "Push a new stack frame when entering a function call.
   Frame contains: {:name :namewhat :line :column :func :frame-env-atom :extraargs :istailcall}
   - func: the actual function object (Lua fn map or Clojure fn)
   - frame-env-atom: atom updated to the live env before each statement (for getlocal)
   - extraargs: number of extra args prepended by __call chain (Lua 5.5 debug.getinfo)
   - namewhat: how the function was called — 'local', 'global', 'field', 'hook', or ''
   - istailcall: true when the function was invoked via tail-call optimisation"
  ([env fn-name line col func-obj frame-env-atom]
   (push-stack-frame! env fn-name line col func-obj frame-env-atom 0 nil false))
  ([env fn-name line col func-obj frame-env-atom extraargs]
   (push-stack-frame! env fn-name line col func-obj frame-env-atom extraargs nil false))
  ([env fn-name line col func-obj frame-env-atom extraargs namewhat]
   (push-stack-frame! env fn-name line col func-obj frame-env-atom extraargs namewhat false))
  ([env fn-name line col func-obj frame-env-atom extraargs namewhat istailcall]
   (when-let [stack-atom (:call-stack env)]
     (swap! stack-atom conj {:name fn-name :namewhat namewhat :line line :column col
                             :func func-obj :frame-env-atom frame-env-atom
                             :extraargs extraargs :istailcall (boolean istailcall)}))))

(defn pop-stack-frame!
  "Pop the top stack frame when exiting a function."
  [env]
  (when-let [stack-atom (:call-stack env)]
    (swap! stack-atom pop)))

(defn get-stack-trace
  "Get the current call stack as a vector of frames.
   Each frame is {:name fn-name :line line :column col}."
  [env]
  (when-let [stack-atom (:call-stack env)]
    @stack-atom))

;; ============================================================================
;; _G (Global environment table)
;; ============================================================================

;; ============================================================================
;; Locale helpers
;; ============================================================================

(defn get-numeric-locale
  "Return the java.util.Locale for the current numeric formatting context.
   Defaults to Locale/ROOT (= C locale) if no locale atom is present."
  [env]
  (if-let [a (:locale-numeric env)]
    (:java-locale @a)
    Locale/ROOT))

(defn get-numeric-locale-name
  "Return the locale name string (e.g. \"C\", \"pt_BR\") for the current numeric locale."
  [env]
  (if-let [a (:locale-numeric env)]
    (:name @a)
    "C"))

(defn set-numeric-locale!
  "Set the numeric locale atom to the given Java Locale and POSIX name string."
  [env ^Locale java-locale locale-name]
  (when-let [a (:locale-numeric env)]
    (reset! a {:java-locale java-locale :name locale-name})))

(defn numeric-decimal-char
  "Return the decimal separator character for the current numeric locale."
  [env]
  (.getDecimalSeparator (DecimalFormatSymbols/getInstance (get-numeric-locale env))))
