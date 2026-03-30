# CLua: Deviations from Standard Lua

This document describes where CLua differs from the Lua 5.5 reference implementation (PUC-Lua).

CLua passes the official Lua 5.5.0 test suite with the deviations noted below.

---

## Unsupported Language Features

| Feature                | Reason                                                      |
|------------------------|-------------------------------------------------------------|
| `__gc` metamethod      | JVM controls garbage collection; finalizers are not exposed |
| `__mode` (weak tables) | Requires JVM `WeakReference` integration; not implemented   |

---

## Library Deviations

### `os`

| Function       | Behaviour                                                                     |
|----------------|-------------------------------------------------------------------------------|
| `os.execute`   | Always returns `nil`. Shell execution not supported.                          |
| `os.exit`      | Terminates the script, not the JVM. Returns `{:ok true/false, :exit-code n}`. |
|                | Code 0 / `true` → `:ok true`; other → `:ok false`. Not catchable by `pcall`.  |
| `os.setlocale` | Returns `nil` for `"collate"` and `"ctype"` categories.                       |
|                | JVM locale collation/classification not exposed.                              |
| `os.getenv`    | Reads from `:env-vars` map at sandbox creation.                               |
|                | Default: `{}`. Never reads real environment variables.                        |
| `os.tmpname`   | In-memory VFS, not the real filesystem.                                       |
| `os.remove`    | In-memory VFS, not the real filesystem.                                       |
| `os.rename`    | In-memory VFS, not the real filesystem.                                       |

### `io`

`io` is VFS-based. All file operations read and write in-memory files. By default there
is no access to the real filesystem — not even in `sandbox-full`. Real files and
directories can be selectively exposed via `clua.vfs/mount`, which maps host paths into
the VFS under caller-chosen names. Scripts see only what is explicitly mounted.

| Handle      | Behaviour                                                            |
|-------------|----------------------------------------------------------------------|
| `io.popen`  | Returns `nil` + error. No subprocess support.                        |
| `io.stdin`  | Backed by an empty in-memory buffer. Reads return EOF immediately.   |
| `io.stdout` | In restricted sandboxes: null device — writes are silently discarded.|
| `io.stderr` | In restricted sandboxes: null device — writes are silently discarded.|

### `string`

| Function      | Behaviour                                   |
|---------------|---------------------------------------------|
| `string.dump` | Throws an error. No bytecode serialisation. |

### `package`

| Entry             | Behaviour                                                |
|-------------------|----------------------------------------------------------|
| `package.loadlib` | Always `nil` + error. No native C extensions on JVM.     |
| `package.cpath`   | Always empty.                                            |
| `require`         | Works for Lua modules in VFS via `stdlib/populate-vfs!`. |
|                   | C modules are not loadable.                              |

### `load` / `loadfile` / `dofile`

Included in `sandbox-full`; not in `sandbox-standard` by default, but can be added
via `:globals`. Nested `load()` calls (loading code from within a loaded chunk)
return `nil` instead of the expected value — an accepted limitation.

### `debug`

The full debug API is implemented. Deviations:

| Feature                                 | Behaviour                                              |
|-----------------------------------------|--------------------------------------------------------|
| `debug.getinfo` `ftransfer`/`ntransfer` | Always `nil`. Argument tracking not feasible on JVM.   |
| Sub-statement debug hook granularity    | Fires per statement; PUC-Lua fires per VM instruction. |

---

## Global Functions

| Function         | Behaviour                                                  |
|------------------|------------------------------------------------------------|
| `collectgarbage` | Reports `0` for all queries. No effect on JVM.             |

---

## Compatibility Extensions

These functions are present beyond the Lua 5.5 spec, retained for compatibility:

| Function                              | Note                       |
|---------------------------------------|----------------------------|
| `math.pow`                            | Retained for compatibility |
| `math.sinh`, `math.cosh`, `math.tanh` | Retained for compatibility |

