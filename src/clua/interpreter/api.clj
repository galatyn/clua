(ns clua.interpreter.api
  "Tree-walking interpreter for Lua AST.

   This interpreter executes the Lua AST in a sandboxed environment.
   No access to file system, network, or other dangerous operations
   is provided unless explicitly added to the environment.

   This namespace provides the public API for the Lua interpreter.
   Implementation is split across sub-namespaces for maintainability:
   - clua.interpreter.types: Type checking and value utilities
   - clua.interpreter.tables: Table operations and metamethods
   - clua.interpreter.operators: Binary and unary operators
   - clua.interpreter.expressions: Expression evaluation
   - clua.interpreter.stack-machine: Stack machine (primary execution engine)
   - clua.interpreter.core: Function calls and top-level entry point"
  (:require [clua.interpreter.core :as core]
            [clua.interpreter.tables :as tables]
            [clua.interpreter.types :as types]))
(set! *warn-on-reflection* true)


;;; Re-export public API functions

;; Type checking
(def lua-type types/lua-type)
(def lua-table? types/lua-table?)
(def lua-truthy? types/lua-truthy?)

;; Table operations
(def make-table tables/make-table)
(def table-get tables/table-get)
(def table-set! tables/table-set!)
(def table-get-with-meta tables/table-get-with-meta)
(def get-metatable tables/get-metatable)
(def set-metatable! tables/set-metatable!)
(def get-metamethod tables/get-metamethod)
(def lua-type-name tables/lua-type-name)

;; Function calls & execution
(def call-function core/call-function)
(def eval-chunk core/eval-chunk)
