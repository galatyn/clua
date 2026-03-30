# CLua

<p align="center"><img src="CLua.PNG" alt="CLua" width="480"/></p>

A [Lua 5.5](https://www.lua.org/manual/5.5/) interpreter written in Clojure for safely executing untrusted scripts.

CLua is designed to let you embed Lua as a scripting/configuration layer inside
Clojure applications. The execution environment is completely sandboxed — scripts
cannot touch the filesystem, network, host process, or anything else outside the
sandbox unless you explicitly grant access. As a JVM library, it is also usable from Java and other JVM languages.

---

## Design Priorities

**1. Safety first.**
CLua is a pure interpreter — no bytecode compilation, no JVM code generation, no
`eval` of host-language code. A Lua script cannot reach Clojure or Java internals,
load native libraries, spawn processes, access the filesystem, or perform any
other privileged operation unless you explicitly grant it. The interpreter is also
entirely single-threaded internally — coroutines are cooperative continuations, not
OS threads, and no background threads are ever spawned. The execution model is fully
deterministic and auditable. This makes CLua suitable for running untrusted,
user-supplied scripts inside your application without a separate process or container.

**2. Compatibility over convenience.**
CLua is not a "Lua-like" language. It targets Lua 5.5 syntax and semantics exactly,
including integer/float type distinction, all bitwise operators, coroutines,
metatables, to-be-closed variables, the full standard library set, and more. Scripts that
run on PUC-Lua 5.5 should run on CLua without modification. The differences listed in
[DEVIATIONS.md](docs/DEVIATIONS.md) are deliberate omissions of features that have no
place in a sandboxed embedding context — subprocess execution, native C extensions,
JVM-incompatible GC hooks.

**3. Performance matters, but safety comes first.**
Pure interpretation is a deliberate trade-off: it keeps the sandbox airtight and
the codebase auditable. Within that constraint, performance is actively worked on.
The target is scripting, configuration, and business-logic workloads inside a JVM
service, not compute-intensive number crunching.

---

## Features

- **Full Lua 5.5 language support** — integers, floats, bitwise ops, coroutines,
  metatables, `goto`, to-be-closed variables, tail-call optimisation, `_ENV`, and more
- **Sandboxed by default** — scripts run in a completely locked-down environment.
  No filesystem, no network, no shell, no reflection, no access to the host process
  or JVM internals. A script can only do what you explicitly hand it — nothing else
  is reachable
- **VFS-based `io.*`** — scripts read and write in-memory files; real files can be
  mounted explicitly (see [File Access](#file-access))
- **Resource limits** — configurable step limit and memory cap per execution
- **Clean result maps** — every call returns `{:ok true :result …}` or
  `{:ok false :error … :line … :column …}`. Never throws
- **Persistent state** — share globals across multiple script runs with `make-state`
- **Call Lua from Clojure** — look up and call Lua functions defined in a previous run
- **Passes the official Lua 5.5 test suite** (with documented deviations — see
  [DEVIATIONS.md](docs/DEVIATIONS.md))
- **Thread-safe by design** — stateless `execute` calls are safe to run concurrently
  from any number of threads with no locking. Many other Lua embedding libraries
  require external synchronisation or per-thread interpreter instances; CLua's
  pure-interpreter model gives you this for free
- **Minimal dependencies** — one runtime dep beyond Clojure: clj-antlr (ANTLR4
  runtime is pulled in transitively)

---

## Installation

```clojure
;; deps.edn
{io.github.galatyn/clua {:mvn/version "0.1.1"}}

;; Leiningen
[io.github.galatyn/clua "0.1.1"]
```

---

## Quick Start

```clojure
(require '[clua.core :as lua]
         '[clua.stdlib.core :as stdlib])

;; Run a script, get a result
(lua/execute "return 1 + 1")
;; => {:ok true, :result 2}

;; Arithmetic, strings, tables
(lua/execute "
  local t = {}
  for i = 1, 5 do t[i] = i * i end
  return t
")
;; => {:ok true, :result {1 1, 2 4, 3 9, 4 16, 5 25}}
;; (Lua tables always come back as Clojure maps — keys match Lua's 1-based indexing)

;; Call a Clojure function from Lua
(lua/execute (stdlib/sandbox-standard)
  {:globals {:name     "world"
             :fn/greet (fn [s] (str "Hello, " s "!"))}}
  "return greet(name)")
;; => {:ok true, :result "Hello, world!"}

;; Errors are returned, not thrown
(lua/execute "return 1 + nil")
;; => {:ok false, :error "attempt to perform arithmetic on a nil value",
;;     :line 1, :column 10}
```

---

## Sandboxes

Three built-in presets for the common cases:

| Sandbox            | Standard libs | Extras | Use when                           |
|--------------------|:-------------:|:------:|------------------------------------|
| `sandbox-minimal`  | no            | no     | Maximum isolation                  |
| `sandbox-standard` | yes           | no     | **Default.** Untrusted scripts     |
| `sandbox-full`     | yes           | yes    | Needs print, load, or other extras |

`sandbox-full` adds these on top of `sandbox-standard`:

- **`print`** — produces visible side effects (output goes to `:output-fn` or stdout)
- **`warn`** — produces visible side effects (output goes to `:warn-fn` or stderr)
- **`load`** — executes dynamically constructed code (not a security concern in CLua, but reduces auditability)
- **`dofile`** / **`loadfile`** — load and execute files from the VFS
- **`debug`** — the full `debug` library

`io` and `os` are included in `sandbox-standard` — both are fully VFS-based and
cannot touch the real filesystem or host environment. In restricted sandboxes
(`sandbox-minimal`, `sandbox-standard`, `make-sandbox`), `io.stdout` and `io.stderr`
are null devices — writes are silently discarded and never reach the real process
streams. Use `sandbox-full` to get real stdout/stderr, or redirect output via
`:output-fn` / `:warn-fn`.

```clojure
;; No sandbox argument — sandbox-standard is used automatically
(lua/execute "return math.sqrt(2)")
;; => {:ok true, :result 1.4142135623730951}

;; Standard — safe for untrusted scripts (same as above, explicit)
(lua/execute (stdlib/sandbox-standard) "return math.sqrt(2)")
;; => {:ok true, :result 1.4142135623730951}

;; Full — adds print, load, and debug on top of standard
(lua/execute (stdlib/sandbox-full) "print('hello')")
;; => {:ok true, :result nil}  (output goes to *output-fn* or stdout)

;; Minimal — builtins only (type, pcall, pairs, …), no standard libraries
(lua/execute (stdlib/sandbox-minimal) "return type(42)")
;; => {:ok true, :result "number"}
```

When the presets don't fit, use `make-sandbox` to specify exactly the libraries you need:

```clojure
(lua/execute (stdlib/make-sandbox #{:string :math :table})
  "return string.upper('hello')")
;; => {:ok true, :result "HELLO"}
```

Standard library keywords:

| Keyword      | Adds          |
|--------------|---------------|
| `:coroutine` | `coroutine.*` |
| `:table`     | `table.*`     |
| `:string`    | `string.*`    |
| `:math`      | `math.*`      |
| `:utf8`      | `utf8.*`      |
| `:debug`     | `debug.*`     |
| `:os`        | `os.*`        |
| `:io`        | `io.*`        |

Individual globals:

| Keyword     | Adds    |
|-------------|---------|
| `:fn/print` | `print` |
| `:fn/warn`  | `warn`  |
| `:fn/load`  | `load`  |

---

## Injecting Variables

Pass Clojure values as Lua globals. Maps and vectors are automatically converted to
Lua tables:

```clojure
(lua/execute (stdlib/sandbox-standard)
  {:globals {:config {:max_retries 3, :timeout 30}}}
  "return config.max_retries * 2")
;; => {:ok true, :result 6}

(lua/execute (stdlib/sandbox-standard)
  {:globals {:prices [10 20 30]}}
  "
  local total = 0
  for _, v in ipairs(prices) do total = total + v end
  return total
")
;; => {:ok true, :result 60}
```

> **Table conversion.** Lua tables always come back as Clojure maps — array entries
> get 1-based integer keys, matching Lua's indexing. String keys become keywords by
> default. Pass `:key-fn identity` to keep string keys as strings, or `:key-fn false`
> to skip conversion entirely and receive raw Lua values.
>
> ```clojure
> (lua/execute "return {10, 20, 30}")
> ;; => {:ok true, :result {1 10, 2 20, 3 30}}
>
> (lua/execute "return {10, 20, 30, x = 99}")
> ;; => {:ok true, :result {1 10, 2 20, 3 30, :x 99}}
>
> (lua/execute {:key-fn identity} "return {x = 1}")
> ;; => {:ok true, :result {"x" 1}}
> ```

---

## Calling Clojure Functions from Lua

Use the `:fn/` prefix on global keys to inject Clojure functions — arguments and return
values are automatically converted between Lua and Clojure:

```clojure
;; Functions can take multiple arguments and return values
(lua/execute (stdlib/sandbox-standard)
  {:globals {:fn/distance (fn [x1 y1 x2 y2]
                            (Math/sqrt (+ (Math/pow (- x2 x1) 2)
                                          (Math/pow (- y2 y1) 2))))}}
  "return distance(0, 0, 3, 4)")
;; => {:ok true, :result 5.0}

;; Side-effecting functions work too — useful for logging, metrics, etc.
(lua/execute (stdlib/sandbox-standard)
  {:globals {:fn/log     (fn [msg] (println "[lua]" msg) nil)
             :fn/compute (fn [x] (* x x))}}
  "
  log('starting')
  local result = compute(42)
  log('done: ' .. tostring(result))
  return result
")
;; => {:ok true, :result 1764}  (also prints "[lua] starting" and "[lua] done: 1764")
```

> `lua/wrap-fn` is available for explicit wrapping when you need it (e.g. wrapping
> a function outside of `:globals`).

The other direction works too — call a Lua-defined function directly from Clojure:

```clojure
(let [state (lua/make-state (stdlib/sandbox-standard))]
  (lua/run state "function add(a, b) return a + b end")
  (lua/call-fn state "add" [3 4]))
;; => {:ok true, :result 7}

;; Capture print output from the called function
(let [state (lua/make-state (stdlib/sandbox-full))
      out   (volatile! [])]
  (lua/run state "function greet(name) print('Hello, ' .. name .. '!') end")
  (lua/call-fn state "greet" ["world"] {:output-fn #(vswap! out conj %)})
  @out)
;; => ["Hello, world!"]
```

---

## Persistent State — Globals Across Runs

Use `make-state` + `run` when you want globals to survive across multiple script
executions (e.g. loading a module once, then calling functions from it repeatedly):

```clojure
(def state (lua/make-state (stdlib/sandbox-standard)))

;; Load definitions
(lua/run state "
  counter = 0
  function increment(n) counter = counter + (n or 1) end
")
;; => {:ok true, :result nil}

;; Call across runs — state persists
(lua/run state "increment(5)")
;; => {:ok true, :result nil}
(lua/run state "increment(3)")
;; => {:ok true, :result nil}

(lua/run state "return counter")
;; => {:ok true, :result 8}
```

---

## Resource Limits

Scripts are bounded by a step limit (number of Lua operations) and a memory cap:

```clojure
;; Default limits: 1,000,000 steps, 10 MB
(lua/execute (stdlib/sandbox-standard)
  {:step-limit   50000
   :memory-limit (* 1024 1024)}     ; 1 MB
  "
  local s = ''
  for i = 1, 1000000 do s = s .. 'x' end
  return s
")
;; => {:ok false, :error "... limit exceeded", ...}
```

---

## Capturing `print` Output

```clojure
(def output (atom []))

(lua/execute (stdlib/sandbox-full)
  {:output-fn (fn [line] (swap! output conj line))}
  "
  print('hello')
  print('world')
")

@output
;; => ["hello" "world"]
```

---

## File Access

Include `:io` in `make-sandbox`, then use `mount` to expose specific real files or
directories. Scripts can only see what you explicitly mount — nothing else on disk is
reachable. `with-sandbox` guarantees cleanup even if the script throws.

```clojure
(require '[clua.core :as lua]
         '[clua.stdlib.core :as stdlib]
         '[clua.stdlib.vfs :as vfs])

;; Read one file
(vfs/with-sandbox [sb (vfs/mount (stdlib/sandbox-standard)
                    [{:type :file :real "/data/config.toml" :vfs "config.toml"}])]
  (lua/execute sb "
    local f = assert(io.open('config.toml', 'r'))
    local content = f:read('a')
    f:close()
    return content
  "))

;; Read a directory, write one output file
(vfs/with-sandbox [sb (vfs/mount (stdlib/sandbox-standard)
                    [{:type :dir  :real "/data/inputs" :vfs "inputs/"}
                     {:type :file :real "/tmp/out.txt" :vfs "out.txt" :read-only? false}])]
  (lua/execute sb "
    for line in io.lines('inputs/data.csv') do
      -- process line
    end
    local f = assert(io.open('out.txt', 'w'))
    f:write('done\n')
    f:close()
  "))
```

For in-memory writes that need to be flushed to disk afterward, `flush-vfs!` is also
available as a low-level utility. See [`examples/real_filesystem_access.clj`](examples/real_filesystem_access.clj)
for advanced usage including write-through and flush patterns.

---

## Error Handling

All `execute`, `run`, and `call-fn` calls return a result map and never throw:

```clojure
{:ok true,  :result <clojure-value>}

{:ok false, :error  "error message",
            :line   42,
            :column 7,
            :stack-trace [{:what "Lua" :source "myscript" :line 42} ...]}
```

Lua errors raised with `error()` are caught and returned the same way:

```clojure
(lua/execute "
  local function check(x)
    if x < 0 then error('negative value: ' .. x) end
    return x * 2
  end
  return check(-5)
")
;; => {:ok false, :error "[string \"\"]:3: negative value: -5", :line 3}
```

---

## Coroutines

Full coroutine support including yield-from-nested-functions. Coroutines are
cooperative continuations — no OS threads or JVM threads are involved. The
entire interpreter is single-threaded; coroutines simply suspend and resume
within the same call.

```clojure
(lua/execute "
  local function producer()
    for i = 1, 3 do
      coroutine.yield(i)
    end
  end

  local co = coroutine.create(producer)
  local results = {}
  while true do
    local ok, v = coroutine.resume(co)
    if not ok or v == nil then break end
    results[#results + 1] = v
  end
  return results
")
;; => {:ok true, :result {1 1, 2 2, 3 3}}
```

---

## Multithreading

Because each `execute` call builds its own isolated environment from a plain Clojure
map, stateless calls are safe to fire concurrently from any number of threads with
zero locking or synchronisation. Other Lua embedding libraries typically require either
a dedicated interpreter instance per thread or explicit locks around every call; CLua
has no such requirement. The sandbox map is a plain Clojure value and can be created
once and shared freely:

```clojure
;; Create the sandbox once, reuse across threads
(def sb (stdlib/sandbox-standard))

(future (lua/execute sb "return compute()"))
(future (lua/execute sb "return compute()"))
```

**`LuaState` — one state per thread, never shared.**
`make-state` creates an environment with mutable atoms for globals, call stack, and
execution counters. Passing the same state to concurrent `run` or `call-fn` calls
is detected and rejected immediately with a clear error:

```clojure
(def state (lua/make-state (stdlib/sandbox-standard)))

;; CLua detects this and throws on the second acquire:
;; "LuaState is already in use by thread "Thread-1".
;;  LuaState cannot be shared across threads."
(future (lua/run state long-script))
(future (lua/run state long-script))   ; throws

;; Correct — one state per thread
(defn run-in-thread [script]
  (future
    (let [state (lua/make-state (stdlib/sandbox-standard))]
      (lua/run state script))))
```

---

## Deviations from Standard Lua

See [docs/DEVIATIONS.md](docs/DEVIATIONS.md) for the full list. The main points:

- `io.popen` — not supported (no subprocess access)
- `os.execute` — always returns nil
- `__gc` metamethod — not supported (JVM controls GC)
- `string.dump` — not supported
- `package.loadlib` — not supported (no native C extensions)

---

## Examples

| File                                                                         | What it shows                                                       |
|------------------------------------------------------------------------------|---------------------------------------------------------------------|
| [`examples/real_filesystem_access.clj`](examples/real_filesystem_access.clj) | Mounting real files/dirs into the VFS, write-through, flush to disk |

---

## Dependencies

CLua has one runtime dependency beyond Clojure itself:

| Artifact                                          | Version | Purpose                                            |
|---------------------------------------------------|---------|----------------------------------------------------|
| [`clj-antlr`](https://github.com/aphyr/clj-antlr) | 0.2.14  | Loads and runs the Lua ANTLR4 grammar from the JVM |

The ANTLR4 runtime is pulled in transitively by clj-antlr.

---

## License

MIT — see [LICENSE](LICENSE).
