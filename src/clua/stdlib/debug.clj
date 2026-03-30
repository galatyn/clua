(ns clua.stdlib.debug
  "Minimal debug library stub for Lua compatibility.

   Only implements the subset needed for test suite compatibility.
   Full debug library features (stack inspection, hooks, etc.) are not
   provided in the sandboxed environment."
  (:require [clojure.string :as str]
            [clua.interpreter.coro-runtime :as coro]
            [clua.interpreter.env :as env]
            [clua.interpreter.tables :as tables]
            [clua.interpreter.types :as types])
  (:import (java.util HashMap LinkedHashMap)))
(set! *warn-on-reflection* true)

(declare collect-upvalue-names effective-upvalue-names get-function-env-value lua-getinfo-impl)

(def ^:private valid-what-chars #{\S \l \u \n \t \L \f \r})

(defn- coroutine-env
  "Return the env of the innermost frame from a suspended coroutine's saved
   expr-stack, or nil if the coroutine has no saved state."
  [co]
  (some-> @(:state co) :expr-stack peek :env))

(defn- lua-function-source
  "Return the raw source string for a Lua function, falling back through
   the closure env and finally to '=(load)'."
  [func]
  (or (:source func)
      (get-in func [:env :chunk-name])
      (get-in func [:env :source])
      "=(load)"))

(defn- short-src-from-source
  "Format a source string into short_src per luaO_chunkid (LUA_IDSIZE = 60)."
  [source]
  (cond
    (nil? source) "?"
    (str/starts-with? source "=")
    (let [name (subs source 1)]
      (if (> (count name) 59) (subs name 0 59) name))
    (str/starts-with? source "@")
    (let [filename (subs source 1)]
      (if (> (count filename) 59)
        (str "..." (subs filename (- (count filename) 56)))
        filename))
    :else
    (let [nl-idx (str/index-of source "\n")
          src (if nl-idx (subs source 0 nl-idx) source)
          ;; [string "..."] has 11 chars overhead, leaving 60-11=49 for content
          max-content 47
          content (if (or nl-idx (> (count src) max-content))
                    (str (subs src 0 (min (count src) max-content)) "...")
                    src)]
      (str "[string \"" content "\"]"))))

(defn- collect-active-lines
  "Walk a function body AST and collect all distinct line numbers with code."
  [body]
  (let [lines (volatile! #{})]
    (letfn [(walk [node]
              (when (map? node)
                (when-let [l (:line node)]
                  (when (pos? (long l)) (vswap! lines conj l)))
                (doseq [v (vals node)]
                  (cond
                    (map? v) (walk v)
                    (sequential? v) (doseq [item v]
                                      (when (map? item) (walk item)))))))]
      (walk body))
    @lines))

(defn lua-getinfo
  "debug.getinfo([co,] f-or-level [, what]) - Get information about a function.

   First argument (optional coroutine):
   - coroutine: inspect that coroutine's call stack
   Then:
   - integer >= 0: inspect call stack at that level (nil if out of range)
   - function (Lua or native): inspect that function directly
   - negative integer: returns nil

   Option string (what) — nil means return all fields:
   'S' source info, 'l' current line, 'n' name, 'u' upvalue/param counts,
   'f' func object, 'L' active lines, 't' tail-call flag.
   Throws for invalid option characters."
  ([level] (lua-getinfo level nil))
  ([co-or-level what-or-nil]
   (if (and (map? co-or-level) (= :lua-coroutine (:type co-or-level)))
     ;; (co, level) — coroutine form with no what → (co, level, nil)
     (lua-getinfo co-or-level what-or-nil nil)
     ;; (level, what) — normal form
     (lua-getinfo-impl co-or-level what-or-nil)))
  ([co level what]
   (if (and (map? co) (= :lua-coroutine (:type co)))
     ;; Coroutine form: read call stack from the coroutine's suspended env
     (do
       (when (and (string? what)
                  (not (every? #(contains? valid-what-chars %) what)))
         (throw (ex-info "bad argument #2 to 'getinfo' (invalid option)"
                         {:type :error})))
       (let [co-env (coroutine-env co)]
         (when co-env
           (let [co-stack (env/get-stack-trace co-env)
                 n-stack (count co-stack)
                 ;; co-mode level: CLua pops yield's frame before suspending,
                 ;; so level 1 = innermost Lua frame (matches PUC-Lua level 1).
                 ;; Formula: idx = n-stack - level  (level 0 → OOB → nil)
                 idx (when (and (integer? level) (>= (long level) 0))
                       (- n-stack (long level)))]
             (when (and (some? idx) (>= (long idx) 0) (< (long idx) n-stack))
               (let [frame (nth co-stack idx)
                     func (:func frame)
                     lua-fn? (and (map? func) (= :lua-function (:type func)))
                     native-fn? (fn? func)
                     info (tables/make-table)
                     all? (nil? what)
                     has? #(or all? (str/includes? what %))]
                 (when (has? "S")
                   (cond
                     lua-fn?
                     (let [src (lua-function-source func)
                           what-val (if (:is-main-chunk func) "main" "Lua")]
                       (tables/table-set! info "what" what-val)
                       (tables/table-set! info "source" src)
                       (tables/table-set! info "short_src" (short-src-from-source src))
                       (tables/table-set! info "linedefined" (or (:line-defined func) -1))
                       (tables/table-set! info "lastlinedefined" (or (:last-line-defined func) -1)))
                     native-fn?
                     (do (tables/table-set! info "what" "C")
                         (tables/table-set! info "source" "[C]")
                         (tables/table-set! info "short_src" "[C]")
                         (tables/table-set! info "linedefined" -1)
                         (tables/table-set! info "lastlinedefined" -1))
                     :else
                     (do (tables/table-set! info "what" "Lua")
                         (tables/table-set! info "source" "=(load)")
                         (tables/table-set! info "short_src" "=(load)")
                         (tables/table-set! info "linedefined" -1)
                         (tables/table-set! info "lastlinedefined" -1))))
                 (when (has? "l")
                   ;; currentline = last line executed in the coroutine when it yielded
                   (tables/table-set! info "currentline"
                                      (if-let [la (:current-line co-env)] @la 0)))
                 (when (has? "n")
                   (tables/table-set! info "name" (:name frame))
                   (tables/table-set! info "namewhat" (or (:namewhat frame) "")))
                 (when (has? "u")
                   (cond
                     lua-fn?
                     (let [nups (if (:is-main-chunk func)
                                  1
                                  (count (effective-upvalue-names func)))]
                       (tables/table-set! info "nups" nups)
                       (tables/table-set! info "nparams" (count (:params func)))
                       (tables/table-set! info "isvararg" (boolean (:varargs func))))
                     native-fn?
                     (do (tables/table-set! info "nups" (or (:clua/nups (meta func)) 0))
                         (tables/table-set! info "nparams" 0)
                         (tables/table-set! info "isvararg" true))
                     :else
                     (do (tables/table-set! info "nups" 0)
                         (tables/table-set! info "nparams" 0)
                         (tables/table-set! info "isvararg" true))))
                 (when (has? "f")
                   (tables/table-set! info "func" func))
                 (when (has? "L")
                   (when lua-fn?
                     (let [base-lines (collect-active-lines (:body func))
                           last-line (:last-line-defined func)
                           all-lines (if (and last-line (pos? (long last-line)))
                                       (conj base-lines last-line)
                                       base-lines)
                           active (tables/make-table)]
                       (doseq [l all-lines]
                         (tables/table-set! active l true))
                       (tables/table-set! info "activelines" active))))
                 (when (has? "t")
                   (tables/table-set! info "istailcall" (boolean (:istailcall frame)))
                   (tables/table-set! info "extraargs" (or (:extraargs frame) 0)))
                 info))))))
     ;; Not a coroutine: treat co as level
     (lua-getinfo-impl co level))))

(defn- lua-getinfo-impl
  "Core implementation of debug.getinfo for the current thread."
  [level what]
   (when (and (string? what)
              (not (every? #(contains? valid-what-chars %) what)))
     (throw (ex-info "bad argument #2 to 'getinfo' (invalid option)"
                     {:type :error})))
   (let [current-env (or env/*current-env* (env/make-env))
         call-stack (env/get-stack-trace current-env)
         ;; Resolve: [func-or-nil, stack-frame-or-nil], or nil for invalid level.
         ;; For integer levels >= 0, always return a pair (frame may be nil when
         ;; the CLua call stack is shallower than PUC-Lua's, which always has at
         ;; least one C frame). Only negative integers return nil.
         resolved
         (cond
           (or (and (map? level) (= :lua-function (:type level))) (fn? level))
           [level nil]
           (and (integer? level) (>= (long level) 0))
           (let [idx (- (count call-stack) 1 (long level))]
             (when (and (>= idx 0) (< idx (count call-stack)))
               (let [frame (nth call-stack idx)]
                 [(:func frame) frame])))                   ; nil when level out of range
           :else nil)]
     (when resolved
       (let [[func stack-frame] resolved
             lua-fn? (and (map? func) (= :lua-function (:type func)))
             native-fn? (fn? func)
             info (tables/make-table)
             all? (nil? what)
             has? #(or all? (str/includes? what %))]
         ;; "S" — source / what / line ranges
         (when (has? "S")
           (cond
             lua-fn?
             (let [src (lua-function-source func)
                   what-val (if (:is-main-chunk func) "main" "Lua")]
               (tables/table-set! info "what" what-val)
               (tables/table-set! info "source" src)
               (tables/table-set! info "short_src" (short-src-from-source src))
               (tables/table-set! info "linedefined" (or (:line-defined func) -1))
               (tables/table-set! info "lastlinedefined" (or (:last-line-defined func) -1)))
             native-fn?
             (do (tables/table-set! info "what" "C")
                 (tables/table-set! info "source" "[C]")
                 (tables/table-set! info "short_src" "[C]")
                 (tables/table-set! info "linedefined" -1)
                 (tables/table-set! info "lastlinedefined" -1))
             :else
             (do (tables/table-set! info "what" "Lua")
                 (tables/table-set! info "source" "=(load)")
                 (tables/table-set! info "short_src" "=(load)")
                 (tables/table-set! info "linedefined" -1)
                 (tables/table-set! info "lastlinedefined" -1))))
         ;; "l" — current line
         ;; For integer levels, currentline is the line in that frame where the
         ;; callee was invoked (stored in callee's stack frame as :line).
         ;; For level 0 (the currently executing function) or function-object mode,
         ;; fall back to the global current-line atom.
         (when (has? "l")
           (tables/table-set! info "currentline"
                              (if (and (integer? level) stack-frame)
                                (let [idx (- (count call-stack) 1 (long level))
                                      callee-idx (inc idx)]
                                  (or (when (< callee-idx (count call-stack))
                                        (:line (nth call-stack callee-idx)))
                                      (when-let [la (:current-line current-env)] @la)
                                      0))
                                (if-let [la (:current-line current-env)] @la 0))))
         ;; "n" — name / namewhat
         (when (has? "n")
           (let [;; Look up name and namewhat from the call-stack frame at this level.
                 ;; For level-based queries the relevant frame is one above the queried level
                 ;; (the frame that contains how THIS function was called).
                 frame-at-level (when (and (integer? level) (>= (long level) 0))
                                  (let [idx (- (count call-stack) 1 (long level))]
                                    (when (and (>= idx 0) (< idx (count call-stack)))
                                      (nth call-stack idx))))
                 fname (or (:name stack-frame) (:name frame-at-level))
                 fnwhat (or (:namewhat stack-frame)
                            (:namewhat frame-at-level)
                            (if fname "global" ""))]
              (tables/table-set! info "name" fname)
             (tables/table-set! info "namewhat" fnwhat)))
         ;; "u" — upvalue / param counts
         (when (has? "u")
           (cond
             lua-fn?
             (let [nups (if (:is-main-chunk func)
                          1
                          (count (effective-upvalue-names func)))]
               (tables/table-set! info "nups" nups)
               (tables/table-set! info "nparams" (count (:params func)))
               (tables/table-set! info "isvararg" (boolean (:varargs func))))
             native-fn?
             (do (tables/table-set! info "nups" (or (:clua/nups (meta func)) 0))
                 (tables/table-set! info "nparams" 0)
                 (tables/table-set! info "isvararg" true))
             :else
             (do (tables/table-set! info "nups" 0)
                 (tables/table-set! info "nparams" 0)
                 (tables/table-set! info "isvararg" true))))
         ;; "f" — the function object itself
         (when (has? "f")
           (tables/table-set! info "func" func))
         ;; "L" — active lines table (Lua functions only; nil for C)
         ;; Includes the lastlinedefined line (the closing 'end') to match PUC-Lua,
         ;; which emits an implicit RETURN on that line.
         (when (has? "L")
           (when lua-fn?
             (let [base-lines (collect-active-lines (:body func))
                   last-line (:last-line-defined func)
                   all-lines (if (and last-line (pos? (long last-line)))
                               (conj base-lines last-line)
                               base-lines)
                   active (tables/make-table)]
               (doseq [l all-lines]
                 (tables/table-set! active l true))
               (tables/table-set! info "activelines" active))))
         ;; "t" — tail call flag and extraargs (Lua 5.5: number of __call chain args)
         (when (has? "t")
           (tables/table-set! info "istailcall" (boolean (:istailcall stack-frame)))
           (tables/table-set! info "extraargs" (or (:extraargs stack-frame) 0)))
         info))))

(defn- format-traceback-frame
  "Format a single call-stack frame into a traceback line string."
  [frame]
  (let [fname (:name frame)
        fwhat (:namewhat frame)
        func  (:func frame)
        line  (:line frame)
        lua-fn? (and (map? func) (= :lua-function (:type func)))
        src (cond
              lua-fn? (short-src-from-source (lua-function-source func))
              (fn? func) "[C]"
              :else "?")
        line-part (when (and (not= src "[C]") (not= src "?")
                             (some? line) (pos? (long line)))
                    (str ":" line))
        location (str src (or line-part ""))
        linedefined (when lua-fn? (:line-defined func))
        description (cond
                      (= fwhat "hook") "hook"
                      (= fname "main chunk") "main chunk"
                      (some? fname) (str "function '" fname "'")
                      (and lua-fn? linedefined (pos? (long linedefined)))
                      (str "function <" src ":" linedefined ">")
                      :else "?")]
    (str "\t" location ": in " description)))

(defn- build-traceback-string
  "Format frames-to-show (vector, oldest first) into a traceback string.
   Displays newest frame first; truncates to 10+11 if more than 21 frames."
  [prefix frames-to-show]
  (let [max-top 10
        max-bot 11
        all-frames (if (seq frames-to-show) (vec (rseq frames-to-show)) [])
        n (count all-frames)
        frame-lines
        (cond
          (zero? n) nil
          (<= n (+ max-top max-bot))
          (map format-traceback-frame all-frames)
          :else
          (let [top (take max-top all-frames)
                bot (take-last max-bot all-frames)
                skip-n (- n max-top max-bot)]
            (concat (map format-traceback-frame top)
                    [(str "\t...\t(skip " skip-n " levels)...")]
                    (map format-traceback-frame bot))))]
    (if frame-lines
      (str prefix "stack traceback:\n" (str/join "\n" frame-lines))
      (str prefix "stack traceback:"))))

;; Synthetic [C] frame for suspended-coroutine tracebacks.
;; In CLua, yield's frame is popped before the coroutine suspends, but PUC-Lua
;; keeps it on the stack.  We synthesize it so level numbering matches.
(def ^:private synthetic-yield-frame
  {:name "yield" :namewhat "field" :func (fn [] nil) :line nil})

(defn lua-traceback
  "debug.traceback([thread,] [message [, level]]) - Return a traceback string.

   - Coroutine first arg: build traceback from coroutine's suspended call stack.
   - Non-string non-nil first arg (non-coroutine): return unchanged.
   - nil or string first arg: prepend to 'stack traceback:' block.
   - level=0: includes the debug.traceback frame in the output.
   - level>0 (default 1): omits debug.traceback from the output."
  ([] (lua-traceback nil 1))
  ([msg] (lua-traceback msg 1))
  ([msg level]
   (cond
     ;; Coroutine as first arg (2-arg call): delegate to 3-arity
     (and (map? msg) (= :lua-coroutine (:type msg)))
     (lua-traceback msg nil 0)
     ;; Non-string, non-nil, non-coroutine: return unchanged
     (and (some? msg) (not (string? msg))) msg
     ;; nil or string: build a traceback by walking the current call stack
     :else
     (let [prefix (if (nil? msg) "" (str msg "\n"))
           level-n (if (and (integer? level) (>= (long level) 0)) (long level) 1)
           call-stack (env/get-stack-trace env/*current-env*)
           ;; When called directly, expressions.clj pushes a "traceback" frame at the
           ;; top of the call stack.  level=0 keeps it; level=1 skips it.
           ;; When called indirectly (e.g. via pcall body), no such frame exists, so
           ;; level=1 (default) should show all real frames (skip-count = 0).
           top-name (:name (last call-stack))
           called-directly? (= "traceback" top-name)
           skip-count (if called-directly? (long level-n) (max 0 (dec (long level-n))))
           n-frames (count call-stack)
           frames-to-show (when (pos? n-frames)
                            (subvec call-stack 0 (max 0 (- n-frames skip-count))))]
       (build-traceback-string prefix (or frames-to-show [])))))
  ([co msg level]
   (if (and (map? co) (= :lua-coroutine (:type co)))
     ;; Coroutine traceback: behaviour depends on coroutine status
     (let [co-state @(:state co)
           co-status (:status co-state)
           prefix (if (nil? msg) "" (str msg "\n"))
           level-n (if (and (integer? level) (>= (long level) 0)) (long level) 0)
           raw-call-stack
           (cond
             ;; Suspended: read from the live expr-stack env (existing behaviour)
             (= :suspended co-status)
             (let [co-env (coroutine-env co)]
               (if co-env (env/get-stack-trace co-env) []))
             ;; Dead with saved snapshot (died with error): use snapshot
             (and (= :dead co-status) (seq (:saved-call-stack co-state)))
             (:saved-call-stack co-state)
             ;; Dead normally or no snapshot
             :else [])
           ;; Synthesize a [C] yield frame only for suspended coroutines:
           ;; CLua pops yield's frame before suspending, but PUC-Lua keeps it.
           call-stack (if (and (= :suspended co-status) (seq raw-call-stack))
                        (conj (vec raw-call-stack) synthetic-yield-frame)
                        (vec raw-call-stack))
           n-frames (count call-stack)
           frames-to-show (subvec call-stack 0 (max 0 (- n-frames level-n)))]
       (build-traceback-string prefix frames-to-show))
     ;; Not a coroutine: treat co as msg
     (lua-traceback co level))))

;; ============================================================================
;; debug.upvalueid
;; ============================================================================

;; Upvalue identity type.
;; Two UpvalueIDs are equal iff they reference the same scope HashMap (by
;; object identity) AND have the same variable name.  This mirrors Lua's
;; lightuserdata semantics for upvalue cell pointers.
(deftype UpvalueID [scope ^String var-name]
  Object
  (equals [_ other]
    (and (instance? UpvalueID other)
         (identical? scope (.scope ^UpvalueID other))
         (.equals var-name (.var-name ^UpvalueID other))))
  (hashCode [_]
    (bit-xor (System/identityHashCode scope) (.hashCode var-name))))

(defn- collect-upvalue-names
  "Collect free variable names from a Lua function body in source order.

   'Free' means: referenced by name but not declared as a param or as a local
   variable within the function's own body.  Nested function definitions are
   not traversed (they have their own upvalue sets).

   Returns a vector of unique names in order of first reference."
  [func]
  (let [param-set (cond-> (set (:params func))
                    (:vararg-name func) (conj (:vararg-name func)))
        collected (volatile! [])
        seen (volatile! param-set)]
    (letfn [(record! [name]
              (when-not (contains? @seen name)
                (vswap! seen conj name)
                (vswap! collected conj name)))

            ;; Walk an expression node.
            (walk-exp [node]
              (when (map? node)
                (case (:type node)
                  :name (record! (:value node))
                  :function-def nil                         ; don't recurse into nested closures
                  ;; field-access: only walk the object, not the field name
                  :field-access (walk-exp (:object node))
                  (doseq [v (vals node)]
                    (cond
                      (map? v) (walk-exp v)
                      (sequential? v) (doseq [item v]
                                        (when (map? item) (walk-exp item))))))))

            ;; Walk a block of statements, tracking locally-declared names.
            ;; Returns updated locals set (for sibling statements within the
            ;; same block).
            (walk-block [stmts locals]
              (reduce (fn [acc stmt] (walk-stmt stmt acc)) locals stmts))

            ;; Walk one statement.  Returns updated locals set.
            (walk-stmt [stmt locals]
              (if-not (and (map? stmt) (:type stmt))
                locals
                (case (:type stmt)
                  ;; local x, y = e1, e2  — walk init exprs first, then
                  ;; add declared names to the local set for later stmts.
                  :local
                  (let [names (mapv :value (-> stmt :names :names))
                        init-vs (some-> stmt :values :values)]
                    (doseq [v init-vs] (walk-exp-in-locals v locals))
                    (into locals names))

                  ;; local function f() ... end  — just register the name.
                  :local-func-def
                  (conj locals (:value (:name stmt)))

                  ;; do ... end  — inner locals don't escape.
                  :do
                  (do (walk-block (:statements (:body stmt)) locals) locals)

                  ;; For everything else: walk all child nodes as expressions
                  ;; (this covers if/while/for/return/assignment/calls etc.).
                  (do
                    (walk-exp-in-locals stmt locals)
                    locals))))

            ;; Walk an expression node but skip names that are in `locals`
            ;; (i.e. locally declared within this function).
            (walk-exp-in-locals [node locals]
              (when (map? node)
                (case (:type node)
                  :name
                  (when-not (contains? locals (:value node))
                    (record! (:value node)))
                  :function-def nil
                  ;; field-access: only walk the object, not the field name
                  :field-access (walk-exp-in-locals (:object node) locals)
                  (doseq [v (vals node)]
                    (cond
                      (map? v) (walk-exp-in-locals v locals)
                      (sequential? v) (doseq [item v]
                                        (when (map? item)
                                          (walk-exp-in-locals item locals))))))))]
      (walk-block (:statements (:body func)) #{})
      @collected)))

(defn- find-upvalue-scope
  "Return the innermost scope HashMap in `env` that contains `name`, or nil."
  [env name]
  (loop [scopes (reverse (:scopes env))]
    (when (seq scopes)
      (let [^HashMap scope (first scopes)]
        (if (.containsKey scope name)
          scope
          (recur (rest scopes)))))))

(defn- effective-upvalue-names
  "Like collect-upvalue-names, but collapses global-reference free variables
   into a single leading '_ENV' entry, matching PUC-Lua's upvalue model where
   _ENV is always upvalue #1 for functions that access any global.

   A free variable is 'global' when find-upvalue-scope returns nil for it
   (it lives in *global-scope*, not in any captured local scope)."
  [func]
  (let [raw-names (collect-upvalue-names func)
        func-env (:env func)
        has-env? (volatile! false)
        true-names (filterv (fn [n]
                              (if (find-upvalue-scope func-env n)
                                true
                                (do (vreset! has-env? true) false)))
                            raw-names)]
    (if @has-env?
      (into ["_ENV"] true-names)
      true-names)))

(defn- get-function-env-value
  "Return the _ENV value (global environment table) for a Lua function.
   For load()-ed chunks with a custom env, returns that env table.
   For functions defined in a 'local _ENV = t' scope, returns t.
   For normal chunks, returns _G from the function's env or the current execution."
  [func]
  (let [func-env (:env func)
        reversed-scopes (reverse (:scopes func-env))
        local-env (some (fn [^HashMap s]
                          (when (.containsKey s "_ENV") (.get s "_ENV")))
                        reversed-scopes)]
    (or local-env
        (when-let [id (:env-table-id func-env)]
          (env/resolve-env-table id))
        (:g-table func-env)
        (when-let [ce env/*current-env*]
          (:g-table ce)))))

(defn lua-upvalueid
  "debug.upvalueid(f, n) - Return a unique ID for the n-th upvalue of f.

   Two IDs compare equal (via Lua's ==) iff they refer to the same upvalue
   cell (i.e. the same scope slot for the same variable name).

   For Lua functions: throws for non-function f or out-of-range n.
   For native Clojure functions: returns a non-nil synthetic ID for n >= 1
   (native functions have opaque upvalues, but the ID is always non-nil)."
  [f n]
  (cond
    (fn? f)
    ;; Native Clojure function: return a non-nil synthetic ID for any n >= 1.
    (when (and (number? n) (integer? n) (>= (long n) 1))
      (UpvalueID. (HashMap.) (str "native-" (System/identityHashCode f) "-" n)))

    (not (and (map? f) (= :lua-function (:type f))))
    (throw (ex-info "bad argument #1 to 'upvalueid' (function expected)"
                    {:type :error}))

    :else
    (let [upvalue-names (collect-upvalue-names f)
          idx (when (and (number? n) (integer? n)) (dec (long n)))]
      (when idx
        (let [li (long idx)]
          (when (and (>= li 0) (< li (count upvalue-names)))
            (when-let [scope (find-upvalue-scope (:env f) (nth upvalue-names li))]
              (UpvalueID. scope (nth upvalue-names li)))))))))

(defn lua-getupvalue
  "debug.getupvalue(f, n) - Return the name and value of f's n-th upvalue.
   Returns [name value] on success, nil if f is not a Lua function or n is
   out of range. Does not throw (unlike upvalueid).
   Upvalue #1 is '_ENV' for any function that accesses globals, matching PUC-Lua.
   Native Clojure functions mirror PUC-Lua C functions: upvalue #1 is named ''."
  [f n]
  (cond
    ;; Native Clojure function: upvalue #1 has name "" (like PUC-Lua C upvalues)
    (and (fn? f) (number? n) (integer? n) (= 1 (long n)))
    ["" nil]

    ;; Main chunk: upvalue #1 is always "_ENV"
    (and (map? f) (:is-main-chunk f)
         (number? n) (integer? n) (= 1 (long n)))
    ["_ENV" (get-function-env-value f)]

    ;; Lua function: enumerate captured upvalues
    (and (map? f) (= :lua-function (:type f))
         (number? n) (integer? n) (pos? (long n)))
    (let [upvalue-names (effective-upvalue-names f)
          idx (dec (long n))
          upvalue-name (nth upvalue-names idx nil)]
      (when upvalue-name
        (if (= upvalue-name "_ENV")
          ["_ENV" (get-function-env-value f)]
          (when-let [scope (find-upvalue-scope (:env f) upvalue-name)]
            [upvalue-name (.get ^HashMap scope upvalue-name)]))))))

(defn lua-setupvalue
  "debug.setupvalue(f, n, val) - Set f's n-th upvalue to val.
   Returns the upvalue name on success, nil if f is not a Lua function,
   n is out of range, or (for _ENV) no local _ENV scope was captured.
   _ENV can be set when the function was defined inside 'do local _ENV = t end'."
  [f n val]
  (when (and (map? f) (= :lua-function (:type f))
             (number? n) (integer? n) (pos? (long n)))
    (let [upvalue-names (effective-upvalue-names f)
          idx (dec (long n))
          upvalue-name (nth upvalue-names idx nil)]
      (when upvalue-name
        (when-let [scope (find-upvalue-scope (:env f) upvalue-name)]
          (.put ^HashMap scope upvalue-name val)
          upvalue-name)))))

(defn lua-upvaluejoin
  "debug.upvaluejoin(f1, n1, f2, n2) - Make f1's n1-th upvalue share the
   same variable cell as f2's n2-th upvalue.

   After the call, reading/writing f1's n1-th upvalue reads/writes the same
   underlying scope slot as f2's n2-th upvalue.

   Throws for non-Lua-function arguments or out-of-range upvalue indices."
  [f1 n1 f2 n2]
  (when-not (and (map? f1) (= :lua-function (:type f1)))
    (throw (ex-info "bad argument #1 to 'upvaluejoin' (function expected)"
                    {:type :error})))
  (when-not (and (map? f2) (= :lua-function (:type f2)))
    (throw (ex-info "bad argument #3 to 'upvaluejoin' (function expected)"
                    {:type :error})))
  (let [names1 (collect-upvalue-names f1)
        names2 (collect-upvalue-names f2)
        idx1 (when (and (number? n1) (integer? n1)) (dec (long n1)))
        idx2 (when (and (number? n2) (integer? n2)) (dec (long n2)))]
    (when-not (and idx1 (let [li1 (long idx1)] (and (>= li1 0) (< li1 (count names1)))))
      (throw (ex-info "bad argument #2 to 'upvaluejoin' (invalid upvalue index)"
                      {:type :error})))
    (when-not (and idx2 (let [li2 (long idx2)] (and (>= li2 0) (< li2 (count names2)))))
      (throw (ex-info "bad argument #4 to 'upvaluejoin' (invalid upvalue index)"
                      {:type :error})))
    (let [name1 (nth names1 idx1)
          name2 (nth names2 idx2)
          scope1 (find-upvalue-scope (:env f1) name1)
          scope2 (find-upvalue-scope (:env f2) name2)]
      (when (and scope1 scope2)
        (env/register-upvalue-join! f1 scope1 name1 scope2 name2))))
  nil)

(defn- make-global-proxy
  "Create a Lua table whose __index/__newindex delegate to *global-scope*.
   Reads and writes go directly to the live global environment."
  []
  (let [proxy (tables/make-table)
        mt (tables/make-table)]
    (tables/table-set! mt "__index"
                       (fn [_t k]
                         (when-let [gs env/*global-scope*]
                           (.get ^HashMap gs k))))
    (tables/table-set! mt "__newindex"
                       (fn [_t k v]
                         (when-let [gs env/*global-scope*]
                           (if (nil? v)
                             (.remove ^HashMap gs k)
                             (.put ^HashMap gs k v)))))
    (tables/set-metatable! proxy mt)
    proxy))

;; _HOOKKEY: a weak-key table used as the key under which hooks are stored
;; in the registry.  PUC-Lua tests check getmetatable(registry._HOOKKEY).__mode == 'k'.
(defonce ^:private hookkey-table
  (let [t (tables/make-table)
        mt (tables/make-table)]
    (tables/table-set! mt "__mode" "k")
    (tables/set-metatable! t mt)
    t))

(defn lua-getregistry
  "debug.getregistry() - Return the Lua registry table.
   registry[1] = main thread, registry[2] = live proxy for _G,
   registry._HOOKKEY = weak-key table (mode 'k')."
  []
  (let [reg (tables/make-table)]
    (tables/table-set! reg 1 coro/main-thread)
    (tables/table-set! reg 2 (make-global-proxy))
    (tables/table-set! reg "_HOOKKEY" hookkey-table)
    reg))

(defn lua-debug-getmetatable
  "debug.getmetatable(obj) - Return the real metatable of obj.
   Unlike the global getmetatable, this bypasses __metatable protection
   and always returns the actual metatable (or nil if there is none).
   Works on all Lua types: tables, strings, numbers, booleans, nil."
  [obj]
  (tables/get-metatable obj))

(defn lua-debug-setmetatable
  "debug.setmetatable(value, table) - Set the metatable of any Lua value.
   Unlike setmetatable, works on all types including basic types (number,
   boolean, nil, string). Returns the value."
  [value mt]
  (if (types/lua-table? value)
    (tables/set-metatable! value mt)
    (tables/set-type-metatable! value mt))
  value)

(defn lua-setuservalue
  "debug.setuservalue(udata, val) - Set the user value of a full userdata.
   In CLua, only maps with :clua-metatable are full userdata. Anything else
   (including upvalue IDs, nil, numbers, etc.) is treated as light userdata
   and raises an error, matching PUC-Lua's 'full userdata expected' message."
  [obj _val]
  (if (and (map? obj) (:clua-metatable obj))
    nil
    (throw (ex-info "bad argument #1 to 'setuservalue' (full userdata expected, got light userdata)"
                    {:type :error}))))

;; ============================================================================
;; debug.getuservalue
;; ============================================================================

(defn lua-getuservalue
  "debug.getuservalue(udata) - Return the user value of a full userdata.
   In CLua there are no full userdata, so this always raises an error."
  [obj]
  (if (and (map? obj) (:clua-metatable obj))
    nil
    (throw (ex-info "bad argument #1 to 'getuservalue' (full userdata expected)"
                    {:type :error}))))

;; ============================================================================
;; debug.debug
;; ============================================================================

(defn lua-debug
  "debug.debug() - Interactive prompt stub.
   Not feasible in a sandboxed environment; returns nil."
  []
  nil)

;; ============================================================================
;; debug.getlocal / debug.setlocal
;; ============================================================================

(defn- enumerate-locals
  "Return a vector of [name ^LinkedHashMap scope] pairs for all
   locals of `func` in declaration order, given the live environment `live-env`.

   Order:
   1. Parameters (from (:params func) in declaration order, found in param-scope)
   2. Locals (all scopes beyond the param scope, in push order = declaration order)

   Vararg '...' is excluded from the enumeration (accessed by negative indices)."
  [func live-env]
  (let [params (or (:params func) [])
        outer-count (long (or (:outer-scope-count live-env) 0))
        all-scopes (:scopes live-env)
        param-scope (when (< outer-count (count all-scopes))
                      (nth all-scopes outer-count))
        local-scopes (when (> (count all-scopes) (unchecked-inc outer-count))
                       (subvec all-scopes (unchecked-inc outer-count)))]
    (into
      ;; params first (declaration order from function definition)
      (into [] (comp (filter #(.containsKey ^LinkedHashMap param-scope %))
                     (map (fn [p] [p param-scope])))
            params)
      ;; then each local scope in push order; each scope has exactly one entry
      (for [^LinkedHashMap scope (or local-scopes [])
            :when (and scope (pos? (.size scope)))
            k (.keySet scope)
            :when (not= k "...")]
        [k scope]))))

(defn lua-getlocal
  "debug.getlocal([thread,] level, localindex) or debug.getlocal(f, localindex)

   Arg shapes:
   - (co, level, n)  — inspect suspended coroutine co at level, index n
   - (level, n)      — inspect call stack at level, index n
   - (func, n)       — return n-th param name of func (no value; func not running)

   Negative n accesses varargs: n=-1 is first vararg, -2 is second, etc.
   Returns (name, value) on success, nil when index is out of range."
  [& args]
  (let [[co level n]
        (cond
          ;; (co, level, n)
          (and (= 3 (count args))
               (map? (first args)) (= :lua-coroutine (:type (first args))))
          args
          ;; (level, n) or (func, n)
          (= 2 (count args))
          [nil (first args) (second args)]
          :else
          (throw (ex-info "bad argument #1 to 'getlocal' (number or function expected)"
                          {:type :error})))]
    (cond
      ;; Function-object mode: just return param name, no value
      (or (and (map? level) (= :lua-function (:type level))) (fn? level))
      (let [func level
            params (when (and (map? func) (= :lua-function (:type func)))
                     (:params func))
            idx (dec (long n))]
        (when (and (>= idx 0) (< idx (count (or params []))))
          (nth params idx)))

      ;; Integer level
      (and (integer? level) (>= (long level) 0))
      (let [current-env (or env/*current-env* (env/make-env))
            ;; For coroutine mode, use the coroutine's suspended env
            target-env (if co (coroutine-env co) current-env)]
        (when-not target-env
          (throw (ex-info "bad argument #1 to 'getlocal' (level out of range)"
                          {:type :error})))
        (let [call-stack (env/get-stack-trace target-env)
              n-stack (count call-stack)
              ;; In coroutine mode the native getlocal frame is on the main thread's
              ;; call-stack, not the coroutine's.  No -1 offset needed.
              ;; In non-coroutine mode the native debug fn is always at the top.
              idx (if co
                    (- n-stack (long level))
                    (- n-stack 1 (long level)))
              ]
          (when-not (and (>= idx 0) (< idx n-stack))
            (throw (ex-info "bad argument #1 to 'getlocal' (level out of range)"
                            {:type :error})))
          (let [frame (nth call-stack idx)
                func-obj (:func frame)
                live-env (if (and (not co) (= (long level) 1))
                           current-env
                           (when-let [ea (:frame-env-atom frame)] @ea))]
            (when (and live-env (and (map? func-obj) (= :lua-function (:type func-obj))))
              (let [locals (enumerate-locals func-obj live-env)
                    ni (long n)]
                (if (pos? ni)
                  ;; Positive index: named locals
                  (let [local-idx (dec ni)]
                    (when (< local-idx (count locals))
                      (let [[lname ^LinkedHashMap lscope] (nth locals local-idx)]
                        [lname (.get lscope lname)])))
                  ;; Negative index: vararg access
                  (let [param-scope (when-let [oc (:outer-scope-count live-env)]
                                      (let [loc (long oc)]
                                        (when (< loc (count (:scopes live-env)))
                                          (nth (:scopes live-env) loc))))
                        varargs (when param-scope
                                  (.get ^LinkedHashMap param-scope "..."))]
                    (when (vector? varargs)
                      (let [va-idx (- (- ni) 1)]
                        (when (< va-idx (count varargs))
                          ["(vararg)" (nth varargs va-idx)]))))))))))

      (and (integer? level) (neg? (long level)))
      (throw (ex-info "bad argument #1 to 'getlocal' (level out of range)"
                      {:type :error}))

      :else
      (throw (ex-info "bad argument #1 to 'getlocal' (number or function expected)"
                      {:type :error})))))

(defn lua-setlocal
  "debug.setlocal([thread,] level, localindex, value)

   Same argument shapes as getlocal but writes `value` to the local.
   Returns the local name on success, nil when index is out of range."
  [& args]
  (let [[co level n val]
        (cond
          ;; (co, level, n, val)
          (and (= 4 (count args))
               (map? (first args)) (= :lua-coroutine (:type (first args))))
          args
          ;; (level, n, val)
          (= 3 (count args))
          [nil (first args) (second args) (nth args 2)]
          :else
          (throw (ex-info "bad argument #1 to 'setlocal' (number expected)"
                          {:type :error})))]
    (cond
      (and (integer? level) (>= (long level) 0))
      (let [current-env (or env/*current-env* (env/make-env))
            target-env (if co (coroutine-env co) current-env)]
        (when-not target-env
          (throw (ex-info "bad argument #2 to 'setlocal' (level out of range)"
                          {:type :error})))
        (let [call-stack (env/get-stack-trace target-env)
              n-stack (count call-stack)
              ;; In coroutine mode the native getlocal/setlocal frame is on the main
              ;; thread's call-stack, not the coroutine's.  No -1 offset needed.
              ;; In non-coroutine mode the native debug fn is always at the top.
              idx (if co
                    (- n-stack (long level))
                    (- n-stack 1 (long level)))]
          (when-not (and (>= idx 0) (< idx n-stack))
            (throw (ex-info "bad argument #2 to 'setlocal' (level out of range)"
                            {:type :error})))
          (let [frame (nth call-stack idx)
                func-obj (:func frame)
                live-env (if (and (not co) (= (long level) 1))
                           current-env
                           (when-let [ea (:frame-env-atom frame)] @ea))]
            (when (and live-env (and (map? func-obj) (= :lua-function (:type func-obj))))
              (let [locals (enumerate-locals func-obj live-env)
                    ni (long n)]
                (if (pos? ni)
                  (let [local-idx (dec ni)]
                    (when (< local-idx (count locals))
                      (let [[lname ^LinkedHashMap lscope] (nth locals local-idx)]
                        (.put lscope lname val)
                        lname)))
                  ;; Negative index: vararg write
                  (let [param-scope (when-let [oc (:outer-scope-count live-env)]
                                      (let [loc (long oc)]
                                        (when (< loc (count (:scopes live-env)))
                                          (nth (:scopes live-env) loc))))
                        varargs (when param-scope
                                  (.get ^LinkedHashMap param-scope "..."))]
                    (when (vector? varargs)
                      (let [va-idx (- (- ni) 1)]
                        (when (< va-idx (count varargs))
                          (.put ^LinkedHashMap param-scope "..."
                                (assoc varargs va-idx val))
                          "(vararg)"))))))))))

      (and (integer? level) (neg? (long level)))
      (throw (ex-info "bad argument #2 to 'setlocal' (level out of range)"
                      {:type :error}))

      :else
      (throw (ex-info "bad argument #2 to 'setlocal' (number expected)"
                      {:type :error})))))

;; ============================================================================
;; debug.sethook / debug.gethook
;; ============================================================================

(defn lua-sethook
  "debug.sethook([thread,] hook, mask [, count])

   Registers a hook function fired for events described by mask:
   'c' = calls, 'r' = returns, 'l' = line events.
   count > 0 fires the hook every count instructions.
   Calling with no hook arg (or nil hook) clears the hook."
  [& args]
  (let [[co hook-fn mask cnt]
        (cond
          ;; (co, fn, mask [, count])
          (and (>= (count args) 2)
               (map? (first args)) (= :lua-coroutine (:type (first args))))
          (let [[c f m n] args] [c f (or m "") (or n 0)])
          ;; (fn, mask [, count]) or ()
          :else
          (let [[f m n] args] [nil f (or m "") (or n 0)]))
        current-env (or env/*current-env* (env/make-env))
        target-env (if co (coroutine-env co) current-env)
        clear-hook? (or (nil? hook-fn) (and (not (fn? hook-fn))
                                            (not (and (map? hook-fn) (= :lua-function (:type hook-fn))))))]
    (if target-env
      ;; Coroutine already running / main thread: install hook directly
      (when-let [hook-atom (:hook target-env)]
        (if clear-hook?
          (reset! hook-atom nil)
          (reset! hook-atom {:fn hook-fn
                             :mask (str mask)
                             :count (long cnt)
                             :stepctr (long-array [0])
                             :lastline (atom (or (when-let [la (:current-line target-env)] @la) -1))})))
      ;; Coroutine not yet started: store as pending-hook in state atom so
      ;; resume-first-run can install it when the coroutine's env is created.
      (when co
        (if clear-hook?
          (swap! (:state co) dissoc :pending-hook)
          (swap! (:state co) assoc :pending-hook {:fn hook-fn
                                                  :mask (str mask)
                                                  :count (long cnt)
                                                  :stepctr (long-array [0])
                                                  :lastline (atom -1)})))))
  nil)

(defn lua-gethook
  "debug.gethook([thread]) - Return current hook settings.

   Returns nil if no hook is set, or (hook-fn, mask, count) as multiple values."
  ([] (lua-gethook nil))
  ([co]
   (let [current-env (or env/*current-env* (env/make-env))
         target-env (if (and co (map? co) (= :lua-coroutine (:type co)))
                      (coroutine-env co)
                      current-env)]
     (when target-env
       (when-let [hook-atom (:hook target-env)]
         (when-let [{:keys [fn mask count]} @hook-atom]
           [fn mask count]))))))

(def debug-lib
  "Debug library functions available in sandbox."
  {"getinfo" lua-getinfo
   "traceback" lua-traceback
   "upvalueid" lua-upvalueid
   "upvaluejoin" lua-upvaluejoin
   "getupvalue" lua-getupvalue
   "setupvalue" lua-setupvalue
   "getregistry" lua-getregistry
   "getmetatable" lua-debug-getmetatable
   "setuservalue" lua-setuservalue
   "getuservalue" lua-getuservalue
   "setmetatable" lua-debug-setmetatable
   "getlocal" lua-getlocal
   "setlocal" lua-setlocal
   "sethook" lua-sethook
   "gethook" lua-gethook
   "debug" lua-debug})
