(ns clua.stdlib.core
  "Safe standard library functions for the Lua interpreter.

   Only includes functions that are safe for sandboxed execution.
   No file I/O, network, or system access is provided."
  (:require [clojure.string :as str]
            [clua.interpreter.env :as env]
            [clua.interpreter.api :as interp]
            [clua.interpreter.tables :as tables]
            [clua.parser.parser :as parser]
            [clua.stdlib.coroutine :as lua-coroutine]
            [clua.stdlib.debug :as lua-debug]
            [clua.stdlib.io :as lua-io]
            [clua.stdlib.math :as lua-math]
            [clua.stdlib.os :as lua-os]
            [clua.stdlib.string :as lua-string]
            [clua.stdlib.table :as lua-table]
            [clua.stdlib.utf8 :as lua-utf8])
  (:import (java.util ArrayList HashMap Iterator Map$Entry)))
(set! *warn-on-reflection* true)

(declare format-source-name make-package-table)

(defn- strip-g-zeros
  "Strip trailing zeros from a Java %g-formatted number string.
   Java's String.format does not strip trailing zeros for %g like C's printf.
   This corrects that by removing trailing zeros and any lone trailing decimal separator."
  [^String s]
  (let [n (.length s)
        e-pos (loop [i 0]
                (cond (>= i n) nil
                      (let [c (.charAt s i)] (or (= c \e) (= c \E))) i
                      :else (recur (inc i))))
        ;; has-decimal?: true iff the mantissa contains a non-digit non-sign char
        ;; (i.e., a decimal separator). Integer-only strings like "72057594037927950"
        ;; must NOT have their significant trailing zeros stripped.
        has-decimal? (fn [^String m]
                       (loop [i (if (and (pos? (.length m))
                                         (let [c (.charAt m 0)]
                                           (or (= c \-) (= c \+)))) 1 0)]
                         (cond (>= i (.length m)) false
                               (not (Character/isDigit (.charAt m i))) true
                               :else (recur (inc i)))))
        strip (fn [^String m]
                (if-not (has-decimal? m)
                  m                                         ;; No decimal separator: integer-only, don't strip significant trailing zeros
                  (let [m2 (str/replace m #"0+$" "")]
                    (if (and (pos? (.length m2))
                             (not (Character/isDigit (.charAt m2 (dec (.length m2))))))
                      (subs m2 0 (dec (.length m2)))
                      m2))))]
    (if e-pos
      (str (strip (subs s 0 e-pos)) (subs s e-pos))
      (strip s))))


;; Note: String, math, table, and utf8 libraries are implemented in their own namespaces:
;; - clua.stdlib.string
;; - clua.stdlib.math
;; - clua.stdlib.table
;; - clua.stdlib.utf8

;;; Basic functions

(defn- lua-type
  "Return the type of a value as a string."
  [v]
  (interp/lua-type v))

(defn- lua-tostring
  "Convert a value to a string, respecting __tostring metamethod."
  [v]
  (cond
    (interp/lua-table? v)
    (if-let [tostring-mm (interp/get-metamethod v "__tostring")]
      (let [result (interp/call-function tostring-mm [v] env/*current-env*)
            result-val (if (vector? result) (first result) result)]
        (when-not (string? result-val)
          (throw (ex-info "'__tostring' must return a string" {:type :error})))
        (str result-val))
      (let [name-str (interp/get-metamethod v "__name")]
        (str (if (string? name-str) name-str "table")
             ": 0x" (Integer/toHexString (System/identityHashCode v)))))

    ;; File handles and other userdata with :clua-metatable
    (and (map? v) (:clua-metatable v))
    (if-let [tostring-mm (interp/get-metamethod v "__tostring")]
      (let [result (interp/call-function tostring-mm [v] env/*current-env*)
            result-val (if (vector? result) (first result) result)]
        (str result-val))
      (let [name-str (interp/get-metamethod v "__name")]
        (str (if (string? name-str) name-str "userdata")
             ": 0x" (Integer/toHexString (System/identityHashCode v)))))

    (or (fn? v) (= :lua-function (:type v)))
    (str "function: " (Integer/toHexString (System/identityHashCode v)))

    (and (map? v) (= :lua-coroutine (:type v)))
    (str "thread: " (Integer/toHexString (System/identityHashCode v)))

    (float? v)
    (let [d (double v)
          loc (env/get-numeric-locale env/*current-env*)
          dec-char (env/numeric-decimal-char env/*current-env*)
          ;; Lua 5.5: try %.14g first; if it doesn't round-trip, use %.17g
          s14 (strip-g-zeros (String/format loc "%.14g" (into-array Object [d])))
          parsed (try (Double/parseDouble (str/replace s14 (str dec-char) "."))
                      (catch NumberFormatException _ nil))
          s (if (and parsed (== (double parsed) d))
              s14
              (strip-g-zeros (String/format loc "%.17g" (into-array Object [d]))))]
      (if (or (str/includes? s (str dec-char)) (re-find #"[eEnN]" s))
        s
        (str s dec-char "0")))

    :else
    (str v)))

(def ^:dynamic *output-fn*
  "When bound to a function, lua-print will call it with the formatted string
   instead of using println. Used by execute/execute-safe to redirect output."
  nil)

(def ^:dynamic *warn-fn*
  "When bound to a function, lua-warn will call it with the warning string
   instead of writing to stderr. Used by execute/execute-safe to redirect warnings."
  nil)

(defn lua-print
  "Print values to stdout (or to *output-fn* when bound).
   Looks up 'tostring' from the GLOBAL scope only (not local scopes), matching Lua
   semantics where print always uses the global tostring, not caller-local shadows."
  [& args]
  (let [current-env env/*current-env*
        ;; Global scope lookup only - never check local scopes
        ;; Falls back to lua-tostring when called outside Lua execution context
        tostring-fn (if env/*global-scope*
                      (.get ^HashMap env/*global-scope* "tostring")
                      lua-tostring)
        convert (fn [v]
                  (cond
                    ;; tostring is nil in global scope: fail with the standard Lua error
                    (nil? tostring-fn)
                    (throw (ex-info "attempt to call a nil value (global 'tostring')"
                                    {:type :error}))
                    ;; tostring is our standard Clojure function: use fast path
                    (identical? tostring-fn lua-tostring)
                    (lua-tostring v)
                    ;; tostring is a custom Lua/Clojure function
                    :else
                    (let [r (interp/call-function tostring-fn [v] current-env)
                          s (if (vector? r) (first r) r)]
                      (when-not (string? s)
                        (throw (ex-info "'tostring' must return a string"
                                        {:type :error})))
                      s)))
        line (apply str (interpose "\t" (map convert args)))]
    (if *output-fn*
      (*output-fn* line)
      (do (.write System/out (.getBytes ^String line "ISO-8859-1"))
          (.write System/out (int \newline))
          (.flush System/out))))
  nil)

(defn- lua-tonumber
  "Convert a value to a number, or nil if not possible."
  ([v]
   (cond
     (number? v) v
     (string? v)
     (let [trimmed (str/trim v)]
       (when (and (seq trimmed) (not (str/includes? v "\u0000")))
         (try
           (cond
             ;; Hex number (float if has dot/locale-decimal or P exponent, integer otherwise)
             (re-matches #"(?i)[+-]?0x.*" trimmed)
             (let [dec-char (env/numeric-decimal-char env/*current-env*)
                   has-frac (or (str/includes? trimmed ".")
                                (str/includes? trimmed (str dec-char))
                                (re-find #"(?i)p" trimmed))]
               (if has-frac
                 ;; Hex float - normalize locale decimal to ".", add p0 if no exponent
                 (let [normalized (if (= dec-char \.)
                                    trimmed
                                    (str/replace trimmed (str dec-char) "."))
                       float-str (if (re-find #"(?i)p" normalized)
                                   normalized
                                   (str normalized "p0"))]
                   (Double/parseDouble float-str))
                 ;; Hex integer - wraps modulo 2^64 (like Lua 5.3)
                 (let [negative? (str/starts-with? trimmed "-")
                       abs-str (if (or negative? (str/starts-with? trimmed "+"))
                                 (subs trimmed 1)
                                 trimmed)
                       mag (BigInteger. (subs abs-str 2) 16)]
                   (.longValue (if negative? (.negate mag) mag)))))
             ;; Decimal: try long first, then double (locale-aware decimal separator)
             :else
             (try (Long/parseLong trimmed)
                  (catch NumberFormatException _
                    (let [dec-char (env/numeric-decimal-char env/*current-env*)
                          normalized (if (= dec-char \.)
                                       trimmed
                                       (str/replace trimmed (str dec-char) "."))]
                      (Double/parseDouble normalized)))))
           (catch Exception _ nil))))
     :else nil))
  ([v base]
   (when (string? v)
     (try
       (Long/parseLong (str/trim v) (int base))
       (catch Exception _ nil)))))

(defn- lua-assert
  "Assert a condition, throwing an error if false.
   On success, returns all arguments (Lua 5.3 semantics)."
  ([]
   (let [msg "bad argument #1 to 'assert' (value expected)"]
     (throw (ex-info msg {:type :error :lua-error msg}))))
  ([v & rest]
   (if (interp/lua-truthy? v)
     (if (seq rest) (vec (cons v rest)) v)
     (let [user-msg (first rest)
           line (when-let [e env/*current-env*]
                  (when-let [a (:current-line e)] @a))
           column (when-let [e env/*current-env*]
                    (when-let [a (:current-column e)] @a))
           ;; When no user message: add 'source:line: ' prefix like PUC-Lua's luaL_error.
           ;; When user message provided: pass through unchanged (like lua_error).
           [msg msg-str]
           (if (seq rest)
             [user-msg (if (string? user-msg) user-msg (str user-msg))]
             (let [source-name (when-let [e env/*current-env*]
                                 (or (:chunk-name e) (:source e)))
                   prefix (when (and line source-name)
                            (str (format-source-name source-name) ":" line ": "))
                   m-str (str prefix "assertion failed!")]
               [m-str m-str]))]
       (throw (ex-info msg-str {:type :assertion-error
                                :line line
                                :column (or column 0)
                                :lua-error msg}))))))

(def ^:const ^:private lua-id-size 60)                      ; LUA_IDSIZE from luaconf.h (includes null terminator)

(defn- format-source-name
  "Convert a Lua source name to a display string, truncated to LUA_IDSIZE-1 (59) chars.
   Mirrors PUC-Lua luaO_chunkid behavior:
   '=name' -> 'name' (keep start, truncate if > 59)
   '@file' -> 'file' (keep end with '...' prefix if > 59)
   'text'  -> '[string \"text\"]' (first line, content limited to fit in 59 chars)"
  [s]
  (when s
    (let [max-len (long (dec lua-id-size))]                 ; 59
      (cond
        (str/starts-with? s "=")
        (let [name (subs s 1)]
          (if (> (count name) max-len)
            (subs name 0 max-len)
            name))
        (str/starts-with? s "@")
        (let [file (subs s 1)
              flen (count file)]
          (if (> flen max-len)
            (str "..." (subs file (- flen (- max-len 3))))
            file))
        :else
        (let [first-line (first (str/split-lines s))
              ;; "[string \"...\"]" = 15 chars overhead; with dots = 15+3-0 = still 15
              ;; total = len("[string \"") + content + len("\"]") = 10 + content + 2 = 12 + content
              ;; max-content = max-len - 12 = 47; if content longer, use 44 chars + "..."
              wrapper-len (long 12)                         ; len of [string ""] without content
              max-content (- max-len wrapper-len)           ; 47
              truncated (if (> (count first-line) max-content)
                          (str (subs first-line 0 (- max-content 3)) "...")
                          first-line)]
          (str "[string \"" truncated "\"]"))))))

(defn- lua-error
  "Raise an error with the given message (any Lua value, not just string).
   Called as error([msg [, level]]) - both args optional.
   level=0: no location prefix; level=1 (default): prefix from call site;
   level N>=2: prefix from N levels up the call stack."
  ([] (throw (ex-info "<no error object>"
                      {:type :error :lua-error "<no error object>"})))
  ([msg] (lua-error msg 1))
  ([msg level]
   (let [cur-env env/*current-env*
         int-level (cond (nil? level) 1 (number? level) (long level) :else 1)
         ;; Determine error location based on level
         [err-line err-source]
         (when (and cur-env (pos? (long int-level)))
           (let [source (or (:chunk-name cur-env) (:source cur-env))
                 current-line (when-let [a (:current-line cur-env)] @a)
                 call-stack @(:call-stack cur-env)]
             (if (= 1 int-level)
               [current-line source]
               ;; Level N>=2: look N-1 into reversed call-stack
               (let [reversed (when (seq call-stack) (rseq (into [] call-stack)))
                     stack-idx (unchecked-dec (long int-level))]
                 (when (and reversed (< stack-idx (count reversed)))
                   [(:line (nth reversed stack-idx)) source])))))
         msg-str (cond
                   (nil? msg) "nil"
                   (string? msg) msg
                   (number? msg) (str msg)
                   (boolean? msg) (str msg)
                   (and (map? msg) (= :lua-function (:type msg)))
                   (str "function: " (Integer/toHexString (System/identityHashCode msg)))
                   (and (map? msg) (= :lua-coroutine (:type msg)))
                   (str "thread: " (Integer/toHexString (System/identityHashCode msg)))
                   :else (str msg))
         formatted-source (format-source-name err-source)
         final-msg (if (and err-line formatted-source)
                     (str formatted-source ":" err-line ": " msg-str)
                     msg-str)]
     (throw (ex-info final-msg {:type :error :line err-line :lua-error msg
                                :error-call-stack (some-> env/*current-env* :call-stack deref vec)})))))

(defn- pcall-error-value
  "Extract the Lua error value from a caught exception.
   For non-string Lua errors (tables, booleans), returns the original value.
   For nil errors, returns '<no error object>' (Lua 5.5 semantics).
   For string errors, returns ex-message which includes any augmentation
   (e.g. '(in metamethod __newindex)' appended by the interpreter)."
  [e]
  (let [data (ex-data e)]
    (if (and data (contains? data :lua-error))
      (let [lua-err (:lua-error data)]
        (cond
          (nil? lua-err) "<no error object>"
          (string? lua-err) (ex-message e)
          :else lua-err))
      (ex-message e))))

(def lua-pcall
  "Protected call - call function and catch errors.
   Uses interpreter's call-function to properly handle both Clojure and Lua functions.
   Tagged with :clua/pcall metadata so the stack machine can intercept it as a frame
   (enabling proper yield-through semantics in coroutines)."
  (with-meta
    (fn [f & args]
      (try
        (let [result (interp/call-function f (vec args) env/*current-env*)]
          (vec (cons true (flatten [result]))))
        (catch StackOverflowError _
          [false "C stack overflow"])
        (catch Exception e
          (if (#{:self-close :exit} (:type (ex-data e)))
            (throw e)                                       ;; self-close and exit must propagate through pcall
            [false (pcall-error-value e)]))))
    {:clua/pcall true}))

(defn- xpcall-invoke-handler
  "Call msgh with err-val, re-invoking on handler errors up to max-depth times.
   Returns the final handler result or 'C stack overflow' if depth exceeded."
  [msgh err-val current-env]
  (loop [val err-val depth 0]
    (if (> depth 200)
      "C stack overflow"
      (let [outcome (try
                      [:ok (let [r (interp/call-function msgh [val] current-env)]
                             (if (vector? r) (first r) r))]
                      (catch StackOverflowError _
                        [:err "C stack overflow"])
                      (catch Exception e
                        (if (#{:self-close :exit} (:type (ex-data e)))
                          (throw e)
                          [:err (pcall-error-value e)])))]
        (if (= :ok (first outcome))
          (second outcome)
          (recur (second outcome) (inc depth)))))))

(def lua-xpcall
  "Extended protected call - call function with custom error handler.
   xpcall(f, msgh, arg1, ...) calls f with args, and if an error occurs,
   calls msgh with the error to transform the error message.
   If the handler itself raises an error, it is re-invoked with the new error,
   up to 200 times (matching LUAI_MAXCCALLS), then 'C stack overflow' is returned.
   Tagged with :clua/xpcall metadata so the stack machine can intercept it as a frame
   (enabling proper yield-through semantics in coroutines)."
  (with-meta
    (fn [f msgh & args]
      (let [current-env env/*current-env*]
        (try
          (let [result (interp/call-function f (vec args) current-env)]
            (vec (cons true (flatten [result]))))
          (catch StackOverflowError _
            [false (xpcall-invoke-handler msgh "C stack overflow" current-env)])
          (catch Exception e
            (if (#{:self-close :exit} (:type (ex-data e)))
              (throw e)                                     ;; self-close and exit must propagate through xpcall
              [false (xpcall-invoke-handler msgh (pcall-error-value e) current-env)])))))
    {:clua/xpcall true}))

(defn- lua-select
  "Return all arguments after argument number index.
   Negative index counts from the end (-1 = last argument).
   Returns multiple values (as a vector) for spreading."
  [index & args]
  (if (= index "#")
    (count args)
    (let [n (count args)
          raw-idx (long index)
          idx (if (neg? raw-idx)
                (+ n raw-idx 1)                             ; -1 -> last, -2 -> second-to-last, etc.
                raw-idx)]
      (when (or (zero? raw-idx) (< idx 1))
        (throw (ex-info "bad argument #1 to 'select' (index out of range)"
                        {:type :error})))
      (vec (drop (dec idx) args)))))

(defn- token-has-bad-escape?
  "Check if an ANTLR string token (starting with \" or ') contains an invalid
   or incomplete escape sequence. Used to distinguish bad-escape errors
   (near '<token>') from unfinished-string errors (near '<eof>')."
  [token]
  (let [n (count token)]
    (loop [i 1]                                             ;; Start at 1 to skip opening quote
      (cond
        (>= i n) false
        (not= \\ (nth token i)) (recur (inc i))
        (>= (inc i) n) true                                 ;; Trailing backslash = bad
        :else
        (let [esc (nth token (inc i))]
          (cond
            (#{\a \b \f \n \r \t \v \\ \" \' \newline \return \z} esc) (recur (+ i 2))
            (Character/isDigit (int esc)) (recur (+ i 2))   ;; \ddd is valid syntax
            (= esc \x)
            (let [h1 (nth token (+ i 2) nil)
                  h2 (nth token (+ i 3) nil)]
              (if (and h1 h2
                       (re-matches #"[0-9a-fA-F]" (str h1))
                       (re-matches #"[0-9a-fA-F]" (str h2)))
                (recur (+ i 4))
                true))                                      ;; Incomplete/invalid hex = bad
            (= esc \u)
            (if (= \{ (nth token (+ i 2) nil))
              (let [close-pos (str/index-of token "}" (+ i 3))]
                (if close-pos (recur (inc (long close-pos))) true))
              true)                                         ;; Missing { = bad
            :else true))))))                                ;; Any other char after \ = bad

(defn- near-from-token
  "Given an ANTLR token recognition error token, produce the 'near ...' message."
  [token]
  (let [last-ch (last token)]
    (if (or (= last-ch \") (= last-ch \'))
      ;; Token ends with a quote → it's a complete/closed string, use as-is
      (str "near '" token "'")
      ;; Token doesn't end with quote → unclosed string
      (if (token-has-bad-escape? token)
        (str "near '" token "'")
        "near '<eof>'"))))

(defn- escape-non-printable-chars
  "Replace non-printable characters (code < 32 or > 126) in s with <\\N> notation.
   Used to format unrecognized-token errors like ANTLR's byte-1 or byte-255 tokens."
  [s]
  (let [sb (StringBuilder.)]
    (run! (fn [^Character c]
            (let [code (int c)]
              (if (or (< code 32) (> code 126))
                (.append sb (str "<\\" code ">"))
                (.append sb c))))
          s)
    (str sb)))

(defn- transform-load-error-msg
  "Transform raw ANTLR/CLua exception messages to Lua-compatible 'near ...' format."
  [msg]
  (when msg
    (cond
      ;; Already has 'near '<EOF>'' — normalize to Lua's 'near <eof>' (lowercase, no quotes)
      (re-find #"near '<EOF>'" msg)
      (str/replace msg "near '<EOF>'" "near <eof>")
      ;; Already has 'near' clause (from parse-escape-sequences fixes)
      (re-find #"near '" msg)
      msg
      ;; Unfinished long string
      (re-find #"mismatched input '\['" msg)
      "near '<eof>'"
      ;; Missing token at EOF (e.g. "missing '}' at '<EOF>'"): produce unquoted <eof>
      ;; to match PUC-Lua's "near <eof>" format (no surrounding quotes).
      (re-find #"missing '[^']+' at '<EOF>'" msg)
      (let [[_ missing-tok] (re-find #"missing '([^']+)' at '<EOF>'" msg)]
        (str "'" missing-tok "' expected near <eof>"))
      ;; Token recognition error(s): extract first token and build near message.
      ;; Must be checked BEFORE extraneous input because ANTLR can produce multi-line
      ;; messages where token recognition errors appear first and extraneous input last.
      (re-find #"token recognition error at:" msg)
      (when-let [[_ tok] (re-find #"token recognition error at: '([^']*)'" msg)]
        (let [escaped (escape-non-printable-chars tok)]
          (if (= escaped tok)
            (near-from-token tok)
            ;; Non-printable char: PUC-Lua says "unexpected symbol near '<\N>'"
            (str "unexpected symbol near '" escaped "'"))))
      ;; Mismatched or extraneous input (unexpected symbol): extract the unexpected token.
      ;; Use greedy .+ to handle tokens that contain quotes (e.g. 'aa' -> ''aa'').
      (re-find #"(?:mismatched|extraneous) input '(.+)' expecting" msg)
      (let [[_ tok] (re-find #"(?:mismatched|extraneous) input '(.+)' expecting" msg)
            ;; Normalize <EOF> to Lua's unquoted <eof> format
            display (if (= tok "<EOF>") "<eof>" (str "'" tok "'"))]
        (str "unexpected symbol near " display))
      ;; "no viable alternative" - parser couldn't match any rule.
      ;; May be accompanied by a "missing 'X' at ..." line indicating what was expected.
      (re-find #"no viable alternative at input '([^']+)'" msg)
      (let [[_ input-str] (re-find #"no viable alternative at input '([^']+)'" msg)
            tokens (str/split (str/trim input-str) #"\s+")
            last-tok (last tokens)
            missing-match (re-find #"missing '([^']+)' at '([^']*)'" msg)
            [_ missing-tok _] (or missing-match [])]
        (if missing-tok
          (str "'" missing-tok "' expected near '" last-tok "'")
          (str "expected token near '" last-tok "'")))
      :else msg)))

(defn- lua-load
  "Compile a Lua chunk and return it as a function.
   load(chunk [, chunkname [, mode [, env]]])

   - chunk: string or reader function returning successive string pieces
   - chunkname: optional name for error messages (default: '=(load)')
   - mode: 't' (text only), 'b' (binary only, unsupported), 'bt'/nil (both)
   - env: optional environment table (or any value) for the loaded chunk

   Returns: compiled function on success, or nil + error message on failure"
  ([chunk]
   (lua-load chunk nil nil nil))
  ([chunk chunkname]
   (lua-load chunk chunkname nil nil))
  ([chunk chunkname mode]
   (lua-load chunk chunkname mode nil))
  ([chunk chunkname mode env-table]
   ;; Validate mode outside try/catch so invalid-mode throws (not returns nil+errmsg)
   (when (and (some? mode) (not (#{"t" "b" "bt" "tb"} (str mode))))
     (throw (ex-info "invalid mode" {:type :error})))
   (try
     ;; Binary-only mode: we only support text, so fail with proper message
     (when (= (str mode) "b")
       (throw (ex-info "attempt to load a text chunk" {:type :error})))

     ;; Collect source code - either from string or reader function
     (let [code (cond
                  (string? chunk)
                  chunk

                  (or (fn? chunk)
                      (and (map? chunk) (= :lua-function (:type chunk))))
                  ;; Reader function (Clojure fn or Lua closure): call repeatedly until nil or ""
                  (loop [parts []]
                    (let [piece (let [r (interp/call-function chunk [] env/*current-env*)]
                                  (if (vector? r) (first r) r))]
                      (cond
                        (nil? piece) (apply str parts)
                        (= piece "") (apply str parts)
                        (string? piece) (recur (conj parts piece))
                        :else (throw (ex-info "reader function must return a string"
                                              {:type :error})))))

                  :else
                  (throw (ex-info "load chunk must be a string or function"
                                  {:type (type chunk)})))

           ;; Parse and transform to AST (empty/whitespace-only source = empty chunk)
           ast (if (str/blank? code)
                 {:type :chunk :body [{:type :block :statements []}]}
                 (parser/parse-and-transform code))

           ;; Get the body from the AST (chunk contains a single block)
           body (if (= :chunk (:type ast))
                  (first (:body ast))
                  ast)

           current-env (or env/*current-env* (env/make-env))

           ;; Store env-table-id to avoid circular refs (works for any value)
           env-table-id (when (some? env-table) (env/register-env-table! env-table))
           ;; Default chunkname: if not provided (nil), use string source (-> [string "..."]).
           ;; Use (some? chunkname) not (or chunkname) since "" is falsy in Clojure but valid in Lua.
           chunk-source (if (some? chunkname)
                          chunkname
                          (if (string? chunk) chunk "=(load)"))
           closure-env (if env-table-id
                         {:scopes []
                          :step-count (:step-count current-env)
                          :step-limit (:step-limit current-env)
                          :memory-used (:memory-used current-env)
                          :memory-limit (:memory-limit current-env)
                          :rng (:rng current-env)
                          :source chunk-source
                          :source-lines nil
                          :current-line (:current-line current-env)
                          :current-column (:current-column current-env)
                          :current-stmt-index (:current-stmt-index current-env)
                          :call-stack (:call-stack current-env)
                          :hook (:hook current-env)
                          :locale-numeric (:locale-numeric current-env)
                          :env-redirect (atom nil)
                          :env-table-id env-table-id}
                         {:scopes []
                          :step-count (:step-count current-env)
                          :step-limit (:step-limit current-env)
                          :memory-used (:memory-used current-env)
                          :memory-limit (:memory-limit current-env)
                          :rng (:rng current-env)
                          :source chunk-source
                          :source-lines nil
                          :current-line (:current-line current-env)
                          :current-column (:current-column current-env)
                          :current-stmt-index (:current-stmt-index current-env)
                          :call-stack (:call-stack current-env)
                          :hook (:hook current-env)
                          :locale-numeric (:locale-numeric current-env)
                          :env-redirect (atom nil)})

           lua-func {:type :lua-function
                     :params []
                     :varargs true                          ; load()ed chunks can receive ... args
                     :body body
                     :env closure-env
                     :source chunk-source
                     ;; Main chunks have linedefined=0 / lastlinedefined=0 (PUC-Lua convention).
                     ;; debug.getinfo uses these; debug.clj skips adding lastlinedefined to
                     ;; activelines when it is not positive, so only real body lines appear.
                     :line-defined 0
                     :last-line-defined 0}]
       lua-func)
     (catch StackOverflowError _
       ;; JVM stack overflow during ANTLR parsing or tree transformation of
       ;; deeply nested source (e.g. 500 levels of do...end).
       (let [source-name (if (some? chunkname) chunkname
                                               (if (string? chunk) chunk "=(load)"))
             formatted-source (format-source-name source-name)]
         [nil (str formatted-source ":1: too many C levels")]))
     (catch Exception e
       ;; Return nil + error message on parse/compile error
       (let [raw-msg (ex-message e)
             data (ex-data e)
             ;; Extract line from ex-data or directly from ANTLR ParseError's errors
             line (or (when data (:line data))
                      (when (instance? clj_antlr.ParseError e)
                        (when-let [first-err (first (.errors ^clj_antlr.ParseError e))]
                          (long (:line first-err))))
                      1)
             clean-msg (transform-load-error-msg raw-msg)
             source-name (if (some? chunkname)
                           chunkname
                           (if (string? chunk) chunk "=(load)"))
             formatted-source (format-source-name source-name)]
         [nil (str formatted-source ":" line ": " clean-msg)])))))

(defn- lua-next
  "next(table [, key]) - stateless table iterator.
   Returns [next-key next-value] or nil if no more entries.
   Array part (keys 1..n) is iterated first, then hash part.
   Throws 'invalid key to next' if key is not found in table."
  ([table] (lua-next table nil))
  ([table key]
   (let [^ArrayList arr (:array table)
         ^HashMap data (:data table)
         arr-size (.size arr)]
     (letfn [(array-key? [k]
               (and (number? k) (let [lk (long k)] (and (pos? lk) (<= lk Integer/MAX_VALUE)))))
             (next-array-from [start-0idx]
               (loop [i (long start-0idx)]
                 (when (< i arr-size)
                   (if-let [v (.get arr i)]
                     [(unchecked-inc i) v]
                     (recur (unchecked-inc i))))))
             (first-hash []
               (let [^Iterator it (.iterator (.entrySet data))]
                 (when (.hasNext it)
                   (let [^Map$Entry e (.next it)]
                     [(tables/denormalize-key (.getKey e)) (.getValue e)]))))
             (next-hash [k]
               ;; Search for k in hash, return entry after it.
               ;; Normalize k so it matches the stored IdentityMapKey wrappers.
               ;; If k is not found (deleted during iteration), return nil gracefully.
               (let [norm-k (tables/normalize-key k)
                     ^Iterator it (.iterator (.entrySet data))
                     found (atom false)]
                 (loop []
                   (when (.hasNext it)
                     (let [^Map$Entry e (.next it)]
                       (if @found
                         [(tables/denormalize-key (.getKey e)) (.getValue e)]
                         (do
                           (when (= (.getKey e) norm-k)
                             (reset! found true))
                           (recur))))))))]
       (cond
         (nil? key)
         (or (next-array-from 0) (first-hash))

         (array-key? key)
         (if (<= (int key) arr-size)
           ;; Key is within array bounds (possibly nil-valued)
           (or (next-array-from (int key)) (first-hash))
           ;; Key exceeds array bounds and not in hash: invalid key
           (if (.containsKey data key)
             (next-hash key)
             (throw (ex-info "invalid key to 'next'" {:type :error}))))

         :else
         ;; Hash key: gracefully handle deleted keys (return nil)
         (next-hash key))))))

(defn- make-pairs-iterator
  "Create a stateful pairs iterator that captures keys at creation time.
   Returns the table as the state value (for compatibility with `y == a` checks)."
  [table]
  (let [hash-data (into {} (:data table))
        ;; Filter out nil-valued array entries (Lua's # and pairs skip nil holes)
        arr-data (into {} (keep-indexed (fn [i v] (when (some? v) [(unchecked-inc (long i)) v]))
                                        (seq (:array table))))
        data (merge hash-data arr-data)
        ;; Normalize keys are stored as-is (IdentityMapKey for Lua fns/tables);
        ;; we denormalize them when returning to Lua code.
        keys-seq (atom (keys data))]
    ;; Iterator ignores state/control args (stateful)
    (fn [& _args]
      (when-let [k (first @keys-seq)]
        (swap! keys-seq rest)
        [(tables/denormalize-key k) (get data k)]))))

(defn- lua-pairs
  "Return an iterator for table key-value pairs.
   Respects __pairs metamethod if present.
   Returns THREE values: iterator function, table (state), nil."
  ([] (throw (ex-info "bad argument #1 to 'pairs' (table expected, got no value)"
                      {:type :error})))
  ([table]
   (if-let [pairs-mm (interp/get-metamethod table "__pairs")]
     ;; __pairs metamethod should return iterator, state, initial
     (interp/call-function pairs-mm [table] env/*current-env*)
     ;; Default: stateful iterator, return table as state (compatible with y==a check)
     [(make-pairs-iterator table) table nil])))

(def ^:private ipairs-stateless-iter-fn
  "Shared stateless ipairs iterator - same function object for all ipairs calls.
   Called as (iter table i) and returns [i+1, table[i+1]] or nil.
   Uses metamethod-aware table access to respect __index."
  (fn [table i]
    (let [next-i (unchecked-inc (long i))
          val (interp/table-get-with-meta table next-i env/*current-env*)]
      (when-not (nil? val)
        [next-i val]))))

(defn- lua-ipairs
  "Return an iterator for array indices and values.
   Respects __ipairs metamethod if present.
   Returns THREE values: iterator function, state, initial value."
  ([] (throw (ex-info "bad argument #1 to 'ipairs' (table expected, got no value)"
                      {:type :error})))
  ([table]
   (if-let [ipairs-mm (interp/get-metamethod table "__ipairs")]
     ;; __ipairs metamethod should return iterator, state, initial
     (interp/call-function ipairs-mm [table] env/*current-env*)
     ;; Default: stateless iterator with table as state, 0 as initial
     [ipairs-stateless-iter-fn table 0])))

;;; Metatable functions

(defn- lua-setmetatable
  "Set the metatable of a table. Returns the table.
   Throws error if table has a protected metatable (__metatable field)."
  [table & [mt]]
  (when-not (interp/lua-table? table)
    (throw (ex-info (str "bad argument #1 to 'setmetatable' (table expected, got "
                         (interp/lua-type table) ")")
                    {:type :error})))
  (when-let [current-mt (interp/get-metatable table)]
    (when (interp/table-get current-mt "__metatable")
      (throw (ex-info "cannot change a protected metatable" {:type :error}))))
  (interp/set-metatable! table mt)
  table)

(defn- lua-getmetatable
  "Get the metatable of a value.
   Returns __metatable field if present, otherwise the actual metatable."
  [v]
  (when-let [mt (interp/get-metatable v)]
    (or (interp/table-get mt "__metatable") mt)))

(defn- lua-rawget
  "Get a value from a table without invoking __index metamethod."
  [table key]
  (interp/table-get table key))

(defn- lua-rawset
  "Set a value in a table without invoking __newindex metamethod.
   Returns the table."
  [table key value]
  (interp/table-set! table key value env/*current-env*)
  table)

(defn- lua-rawequal
  "Compare two values for equality without invoking __eq metamethod."
  [a b]
  (= a b))

(defn- lua-rawlen
  "Get the length of a string or table without invoking __len metamethod.
   Raises an error for any other type."
  [v]
  (cond
    (string? v) (count v)
    (interp/lua-table? v) (.size ^ArrayList (:array v))     ; ArrayList.size() - no deref
    :else (throw (ex-info (str "table or string expected, got " (interp/lua-type v))
                          {:type :error}))))

;;; Build standard globals

(defn- make-lua-table-from-map
  "Convert a Clojure map to a Lua table."
  [m]
  (let [t (interp/make-table)]
    (doseq [[k v] m]
      (interp/table-set! t k v))
    t))

(defn- get-package-table
  "Return the current sandbox's package table (a Lua table), or nil."
  []
  (when env/*global-scope*
    (let [pkg (.get ^HashMap env/*global-scope* "package")]
      (when (interp/lua-table? pkg) pkg))))

(defn- cache-in-package-loaded!
  "Cache result in package.loaded[modname], if the loaded table is available."
  [modname result]
  (when-let [pkg (get-package-table)]
    (when-let [loaded (interp/table-get pkg "loaded")]
      (when (interp/lua-table? loaded)
        (interp/table-set! loaded modname result)))))

(defn- check-package-loaded
  "Return package.loaded[modname] if already cached, nil otherwise."
  [modname]
  (when-let [pkg (get-package-table)]
    (when-let [loaded (interp/table-get pkg "loaded")]
      (when (interp/lua-table? loaded)
        (interp/table-get loaded modname)))))


(defn- strip-shebang-and-bom
  "Pre-process a Lua source string: strip UTF-8 BOM (\\xEF\\xBB\\xBF) and
   replace a leading shebang line (#...) with '--' to make it valid Lua."
  [source]
  (let [s (if (str/starts-with? source "\uFEFF")
            (subs source 1)
            ;; Also handle raw byte BOM: \xEF\xBB\xBF
            (if (and (>= (count source) 3)
                     (= (int (nth source 0)) 0xEF)
                     (= (int (nth source 1)) 0xBB)
                     (= (int (nth source 2)) 0xBF))
              (subs source 3)
              source))]
    (if (str/starts-with? s "#")
      (let [nl (str/index-of s "\n")]
        (if nl
          (str "--" (subs s nl))
          "--\n"))                                          ;; trailing newline makes it valid Lua
      s)))

(defn- build-lua-fn-for-source
  "Parse source and return a :lua-function map ready for call-function.
   Optional env-table-id sets the chunk's _ENV to the registered table
   (pass nil for default global env)."
  ([source chunk-source cur-env]
   (build-lua-fn-for-source source chunk-source cur-env nil))
  ([source chunk-source cur-env env-table-id]
   (let [ast (parser/parse-and-transform source)
         body (if (= :chunk (:type ast)) (first (:body ast)) ast)
         base {:scopes []
               :g-table (:g-table cur-env)
               :step-count (:step-count cur-env)
               :step-limit (:step-limit cur-env)
               :memory-used (:memory-used cur-env)
               :memory-limit (:memory-limit cur-env)
               :rng (:rng cur-env)
               :source chunk-source
               :source-lines nil
               :current-line (:current-line cur-env)
               :current-column (:current-column cur-env)
               :current-stmt-index (:current-stmt-index cur-env)
               :call-stack (:call-stack cur-env)
               :locale-numeric (:locale-numeric cur-env)
               :type-metatables (:type-metatables cur-env)}]
     {:type :lua-function
      :params []
      :varargs true
      :body body
      :env (if env-table-id (assoc base :env-table-id env-table-id) base)
      :source chunk-source})))

(defn- make-dofile
  "Create a dofile function that reads and executes files from the given vfs."
  [vfs]
  (fn [path]
    (let [p (str path)
          mf (get @vfs p)]
      (when-not mf
        (throw (ex-info (str "cannot open '" p "': No such file or directory")
                        {:type :error})))
      (let [source-raw (lua-io/fb-read-all-string mf)
            source (strip-shebang-and-bom source-raw)
            cur-env env/*current-env*
            chunk-name (str "@" p)
            lua-fn (build-lua-fn-for-source source chunk-name cur-env)]
        (interp/call-function lua-fn [] cur-env)))))

(defn- make-loadfile
  "Create a loadfile function that loads files from the given vfs.
   Signature: loadfile([filename [, mode [, env]]])
   When env is explicitly provided (even as nil) it becomes the chunk's _ENV.
   When env is absent the chunk uses the default global environment."
  [vfs]
  (fn [path & rest-args]
    (let [p (str path)
          mf (get @vfs p)]
      (if-not mf
        [nil (str p ": No such file or directory")]
        (let [source-raw (lua-io/fb-read-all-string mf)
              mode (first rest-args)
              ;; Binary chunk detection: Lua bytecode starts with ESC (0x1B)
              is-binary? (and (pos? (count source-raw))
                              (= (int (.charAt ^String source-raw 0)) 0x1B))]
          (cond
            ;; Text-only mode but file is a binary chunk
            (and (= mode "t") is-binary?)
            [nil (str p ": attempt to load a binary chunk")]

            ;; Binary-only mode but file is text (CLua cannot run binary either)
            (= mode "b")
            [nil (str p ": attempt to load a text chunk")]

            ;; Binary chunk with no mode restriction — CLua cannot execute bytecode
            is-binary?
            [nil (str p ": attempt to load a binary chunk")]

            :else
            (try
              (let [source (strip-shebang-and-bom source-raw)
                    cur-env env/*current-env*
                    chunk-name (str "@" p)
                    ;; env is the 3rd arg (index 2 in rest-args); distinguish
                    ;; "not provided" from "explicitly nil" via count check.
                    env-provided? (>= (count rest-args) 2)
                    env-table-id (when env-provided?
                                   (env/register-env-table! (second rest-args)))
                    lua-fn (build-lua-fn-for-source source chunk-name cur-env env-table-id)]
                lua-fn)
              (catch Exception e
                [nil (str p ": " (ex-message e))]))))))))

(defn- package-searchpath
  "Search for modname in path (semicolon-separated templates using '?').
   Returns [filename nil] if found in vfs, or [nil errmsg] if not found.
   sep/rep: replace sep in modname with rep before substitution (default '.'→'/')."
  [vfs modname path sep rep]
  (let [sep (or sep ".")
        rep (or rep "/")
        modname (str/replace (str modname) sep rep)
        errors (StringBuilder.)]
    (loop [templates (str/split (str path) #";")]
      (if (empty? templates)
        [nil (str errors)]
        (let [tmpl (first templates)
              filename (str/replace tmpl "?" modname)]
          (if (contains? @vfs filename)
            [filename nil]
            (do
              (.append errors (str "\n\tno file '" filename "'"))
              (recur (rest templates)))))))))


(defn- lua-require
  "require(modname) - Load a module.

   Lua 5.4 semantics: checks package.loaded, then iterates package.searchers.
   Falls back to built-in modules when no package table is present (minimal sandbox)."
  [modname]
  ;; 1. Check package.loaded cache (truthy value = already loaded)
  (let [cached (check-package-loaded modname)]
    (if (some? cached)
      cached
      (let [pkg (get-package-table)
            searchers (when pkg (interp/table-get pkg "searchers"))]
        (if (interp/lua-table? searchers)
          ;; 2. Iterate package.searchers (Lua 5.4 standard path)
          (let [errors (StringBuilder.)]
            (loop [i 1]
              (let [searcher (interp/table-get searchers i)]
                (if (nil? searcher)
                  (throw (ex-info (str "module '" modname "' not found:" errors)
                                  {:type :error}))
                  (let [result (interp/call-function searcher [modname] env/*current-env*)
                        [v1 v2] (if (vector? result)
                                  [(first result) (second result)]
                                  [result nil])]
                    (cond
                      ;; Searcher returned a loader function
                      (or (fn? v1) (and (map? v1) (= :lua-function (:type v1))))
                      (let [call-args (if (some? v2) [modname v2] [modname])
                            raw (interp/call-function v1 call-args env/*current-env*)
                            result (if (vector? raw) (first raw) raw)
                            cached (if (nil? result) true result)]
                        (cache-in-package-loaded! modname cached)
                        cached)
                      ;; Searcher returned an error string - collect and continue
                      (string? v1)
                      (do (.append errors v1) (recur (inc i)))
                      ;; nil or unexpected - skip
                      :else
                      (recur (inc i))))))))
          ;; Fallback: built-in modules (used when no full sandbox is in scope)
          (case modname
            "debug" (let [m (make-lua-table-from-map lua-debug/debug-lib)]
                      (cache-in-package-loaded! modname m) m)
            "utf8" (let [m (make-lua-table-from-map lua-utf8/utf8-lib)]
                     (cache-in-package-loaded! modname m) m)
            "io" (let [m (lua-io/make-io-table (atom {}))]
                   (cache-in-package-loaded! modname m) m)
            (throw (ex-info (str "module '" modname "' not found") {:type :error}))))))))

(def ^:private collectgarbage-valid-opts
  #{"collect" "stop" "restart" "count" "step" "setpause" "setstepmul" "isrunning"})

(defn- lua-collectgarbage
  "collectgarbage([opt [, arg]]) - no-op in CLua (GC is handled by JVM).
   Validates the option but otherwise returns 0 as a safe approximation."
  ([] 0)
  ([opt]
   (when (and (some? opt) (not (collectgarbage-valid-opts opt)))
     (throw (ex-info (str "bad argument #1 to 'collectgarbage' (invalid option '" opt "')")
                     {:type :error})))
   0)
  ([opt _arg]
   (when (and (some? opt) (not (collectgarbage-valid-opts opt)))
     (throw (ex-info (str "bad argument #1 to 'collectgarbage' (invalid option '" opt "')")
                     {:type :error})))
   0))

(def ^:private warn-enabled (atom true))

(defn lua-warn
  "warn(msg, ...) - Issue a warning message (Lua 5.4).
   Concatenates all arguments and writes 'Lua warning: <msg>' to stderr.
   Control messages '@on' and '@off' enable/disable warnings respectively.
   Non-string arguments raise an error."
  [& args]
  (doseq [[i arg] (map-indexed vector args)]
    (when-not (string? arg)
      (throw (ex-info (str "bad argument #" (unchecked-inc (long i)) " to 'warn' (string expected, got "
                           (interp/lua-type arg) ")")
                      {:type :error}))))
  (let [msg (apply str args)]
    (cond
      (= msg "@on") (reset! warn-enabled true)
      (= msg "@off") (reset! warn-enabled false)
      @warn-enabled (let [line (str "Lua warning: " msg)]
                      (if *warn-fn*
                        (*warn-fn* line)
                        (binding [*out* *err*]
                          (println line))))))
  nil)

(defn sandbox-minimal
  "Minimal sandboxed environment — builtins only, no standard libraries.

   Use case: Maximum isolation. Compute-only scripts with no side effects.
   Provides only:
   - Type checking: type
   - Type conversion: tostring, tonumber
   - Error handling: error, pcall, xpcall, assert
   - Metatable access: getmetatable, setmetatable, rawget, rawset, rawequal, rawlen
   - Table iteration: pairs, ipairs, select, next

   Returns: Map of global name -> function suitable for :sandbox parameter."
  []
  {"type" lua-type
   "tostring" lua-tostring
   "tonumber" lua-tonumber
   "assert" lua-assert
   "error" lua-error
   "pcall" lua-pcall
   "xpcall" lua-xpcall
   "select" lua-select
   ;; "load" intentionally omitted — excluded for auditability, not security
   "next" lua-next
   "pairs" lua-pairs
   "ipairs" lua-ipairs
   "setmetatable" lua-setmetatable
   "getmetatable" lua-getmetatable
   "rawget" lua-rawget
   "rawset" lua-rawset
   "rawequal" lua-rawequal
   "rawlen" lua-rawlen
   "require" lua-require
   "_VERSION" "Lua 5.5"})

(defn sandbox-standard
  "Standard sandboxed environment — all libraries, no print or load.

   Use case: RECOMMENDED DEFAULT for untrusted scripts.
   Provides all standard libraries including io and os. Both are fully
   VFS-based — scripts cannot touch the real filesystem, environment, or
   host process. The VFS starts empty; use vfs/mount to expose real files.

   Excludes print (no visible side effects) and load (for auditability).
   Scripts can only interact through explicitly provided :globals functions.

   Returns: Map of global name -> function suitable for :sandbox parameter."
  []
  (let [string-tbl (make-lua-table-from-map lua-string/string-lib)
        string-mt  (interp/make-table)
        vfs        (atom {})
        pkg        (make-package-table vfs)
        io-tbl     (lua-io/make-io-table vfs)
        os-tbl     (make-lua-table-from-map (lua-os/make-os-table vfs {}))]
    ;; Register the string type metatable so getmetatable("") returns it.
    ;; In standard Lua the string library always sets this up on load.
    (interp/table-set! string-mt "__index" string-tbl)
    (tables/set-type-metatable! "" string-mt)
    (let [sb (merge (sandbox-minimal)
                    {"string"   string-tbl
                     "math"     (make-lua-table-from-map lua-math/math-lib)
                     "table"    (make-lua-table-from-map lua-table/table-lib)
                     "utf8"     (make-lua-table-from-map lua-utf8/utf8-lib)
                     "coroutine" (make-lua-table-from-map lua-coroutine/coroutine-lib)
                     "io"       io-tbl
                     "os"       os-tbl
                     "package"  pkg})]
      (let [loaded (interp/table-get pkg "loaded")]
        (doseq [[k v] sb]
          (when (interp/lua-table? v)
            (interp/table-set! loaded k v))))
      sb)))

(defn- lua-package-searchpath
  "package.searchpath(name, path [, sep [, rep]]) - Search for a module file.
   Returns filename if found in VFS, or nil + error message if not found."
  [vfs name path & [sep rep]]
  (let [[filename err] (package-searchpath vfs (str name) (str path) sep rep)]
    (if filename filename [nil err])))

(defn- make-package-table
  "Create the initial Lua package table with preload, loaded, path, cpath, config,
   searchpath, and a hidden :vfs reference for require to use."
  [vfs]
  (let [pkg (interp/make-table)
        preload (interp/make-table)
        loaded (interp/make-table)]
    (interp/table-set! pkg "preload" preload)
    (interp/table-set! pkg "loaded" loaded)
    ;; Module search path: VFS-relative templates (./?.lua and ./init.lua pattern)
    (interp/table-set! pkg "path" "./?.lua;./?/init.lua")
    ;; C extension search: empty — CLua has no C extension loader
    (interp/table-set! pkg "cpath" "")
    ;; Path configuration string: dir-sep, path-sep, placeholder, exec-mark, ignore-mark
    (interp/table-set! pkg "config" "/\n;\n?\n!\n-")
    ;; searchpath function (VFS-aware)
    (interp/table-set! pkg "searchpath"
                       (fn [name path & args] (apply lua-package-searchpath vfs name path args)))
    ;; loadlib — loads native C libraries; not supported in the JVM sandbox
    (interp/table-set! pkg "loadlib"
                       (fn [& _] [nil "dynamic libraries not supported" "absent"]))
    ;; package.searchers — the standard Lua 5.4 searcher chain used by require
    (let [searchers (interp/make-table)]
      ;; Searcher 1: look in package.preload
      (interp/table-set! searchers 1
                         (fn [modname]
                           (let [preload (interp/table-get pkg "preload")]
                             (if-let [loader (and (interp/lua-table? preload)
                                                  (interp/table-get preload modname))]
                               loader
                               (str "\n\tno field package.preload['" modname "']")))))
      ;; Searcher 2: Lua source file via package.path
      (interp/table-set! searchers 2
                         (fn [modname]
                           (let [path (interp/table-get pkg "path")]
                             (if-not (string? path)
                               "\n\t'package.path' is not a string"
                               (let [[filename err] (package-searchpath vfs modname path nil nil)]
                                 (if filename
                                   ;; Return [loader-fn, filename] pair
                                   [(fn [_mn _fname]
                                      (let [mf (get @vfs filename)
                                            source-raw (lua-io/fb-read-all-string mf)
                                            source (strip-shebang-and-bom source-raw)
                                            cur-env env/*current-env*
                                            lua-fn (build-lua-fn-for-source source (str "@" filename) cur-env)
                                            raw (interp/call-function lua-fn [modname] cur-env)]
                                        (if (vector? raw) (first raw) raw)))
                                    filename]
                                   err))))))
      ;; Searcher 3: C library via package.cpath (not supported; returns search-path errors)
      (interp/table-set! searchers 3
                         (fn [modname]
                           (let [cpath (interp/table-get pkg "cpath")]
                             (if (or (nil? cpath) (str/blank? (str cpath)))
                               "\n\tpackage.cpath is empty"
                               (let [modname-rep (str/replace (str modname) "." "/")
                                     sb (StringBuilder.)]
                                 (doseq [tmpl (str/split (str cpath) #";")
                                         :when (not (str/blank? tmpl))]
                                   (.append sb (str "\n\tno file '" (str/replace tmpl "?" modname-rep) "'")))
                                 (str sb))))))
      (interp/table-set! pkg "searchers" searchers))
    ;; Hidden Clojure reference so lua-require can access the VFS atom
    (interp/table-set! pkg "vfs" vfs)
    pkg))

(defn- sandbox-vfs
  "Extract the VFS atom from a sandbox, or nil if not present."
  [sandbox]
  (when-let [pkg (get sandbox "package")]
    (when (interp/lua-table? pkg)
      (let [vfs (interp/table-get pkg "vfs")]
        (when (instance? clojure.lang.Atom vfs)
          vfs)))))

(defn sandbox-full
  "Full sandboxed environment — sandbox-standard plus print, load, and debug.

   Use case: Development, testing, or scripts that need print output or
   dynamic code loading.
   Adds print (visible output), load (dynamic code execution), and debug.*
   on top of sandbox-standard. All io and os remain fully VFS-based.

   env-vars: optional map of string→string exposed via os.getenv.
   Example: (sandbox-full {\"DATABASE_URL\" \"postgres://...\"})

   Returns: Map of global name -> function suitable for :sandbox parameter."
  ([] (sandbox-full {}))
  ([env-vars]
   (let [sb  (sandbox-standard)
         vfs (sandbox-vfs sb)
         sb  (cond-> (assoc sb
                       "print"          lua-print
                       "warn"           lua-warn
                       "load"           lua-load
                       "collectgarbage" lua-collectgarbage
                       "debug"          (make-lua-table-from-map lua-debug/debug-lib)
                       "io"             (lua-io/make-io-table vfs {:real-stdout? true})
                       "dofile"         (make-dofile vfs)
                       "loadfile"       (make-loadfile vfs))
               (seq env-vars) (assoc "os" (make-lua-table-from-map (lua-os/make-os-table vfs env-vars))))
         loaded (interp/table-get (get sb "package") "loaded")]
     (doseq [[k v] sb]
       (when (interp/lua-table? v)
         (interp/table-set! loaded k v)))
     sb)))

(defn make-sandbox
  "Build a sandbox from a set of feature keywords.

  Library keywords (correspond to Lua standard libraries):
    :coroutine  coroutine.*
    :table      table.*
    :io         io.* + VFS (required before calling mount)
    :os         os.*  (VFS-enabled when :io is also present)
    :string     string.*
    :math       math.*
    :utf8       utf8.*
    :debug      debug.*

  Extra keywords:
    :fn/print   the print function
    :fn/warn    the warn function
    :fn/load    the load function

  When :io is included a shared VFS atom is created automatically.
  When both :io and :os are present they share the same VFS.

  Examples:
    (make-sandbox #{:string :math :table})
    (make-sandbox #{:string :math :io})            ; then use mount
    (make-sandbox #{:string :math :io :fn/print})"
  [features]
  (let [needs-vfs? (contains? features :io)
        vfs        (when needs-vfs? (atom {}))
        pkg        (when needs-vfs? (make-package-table vfs))
        sb         (cond-> (sandbox-minimal)
                     (contains? features :string)
                     (merge (let [string-tbl (make-lua-table-from-map lua-string/string-lib)
                                  string-mt  (interp/make-table)]
                              (interp/table-set! string-mt "__index" string-tbl)
                              (tables/set-type-metatable! "" string-mt)
                              {"string" string-tbl}))
                     (contains? features :math)
                     (assoc "math" (make-lua-table-from-map lua-math/math-lib))
                     (contains? features :table)
                     (assoc "table" (make-lua-table-from-map lua-table/table-lib))
                     (contains? features :utf8)
                     (assoc "utf8" (make-lua-table-from-map lua-utf8/utf8-lib))
                     (contains? features :coroutine)
                     (assoc "coroutine" (make-lua-table-from-map lua-coroutine/coroutine-lib))
                     (contains? features :debug)
                     (assoc "debug" (make-lua-table-from-map lua-debug/debug-lib))
                     (contains? features :os)
                     (assoc "os" (if needs-vfs?
                                   (make-lua-table-from-map (lua-os/make-os-table vfs {}))
                                   (make-lua-table-from-map lua-os/os-lib)))
                     needs-vfs?
                     (assoc "io"       (lua-io/make-io-table vfs)
                            "package"  pkg
                            "dofile"   (make-dofile vfs)
                            "loadfile" (make-loadfile vfs))
                     (contains? features :fn/print)
                     (assoc "print" lua-print)
                     (contains? features :fn/warn)
                     (assoc "warn" lua-warn)
                     (contains? features :fn/load)
                     (assoc "load" lua-load))]
    (when pkg
      (let [loaded (interp/table-get pkg "loaded")]
        (doseq [[k v] sb]
          (when (interp/lua-table? v)
            (interp/table-set! loaded k v)))))
    sb))

