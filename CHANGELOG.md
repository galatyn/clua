# Changelog

## [Unreleased]

## [0.1.0] — 2026-03-30

### Added
- Full Lua 5.5 language support — integers, floats, bitwise operators, coroutines,
  metatables, `goto`, to-be-closed variables, tail-call optimisation, `_ENV`
- Three sandbox levels: `sandbox-minimal`, `sandbox-standard`, `sandbox-full`
- VFS-based `io.*` — all file operations use an in-memory virtual filesystem
- Real filesystem mounting via `mount-file!`, `mount-dir!`, `flush-vfs!`
- Resource limits: configurable step limit and memory cap per execution
- Persistent state via `make-state` / `run` / `call-fn`
- Thread-ownership guard on `LuaState` — concurrent misuse detected and rejected
- Passes the official Lua 5.5 test suite (with documented deviations)
