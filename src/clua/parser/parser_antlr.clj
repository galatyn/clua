(ns clua.parser.parser-antlr
  "Experimental ANTLR4-based parser for Lua.
   Uses grammars from antlr/grammars-v4 repo."
  (:require [clj-antlr.core :as antlr]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [clua.parser.antlr-transform :as transform]
            [clua.parser.grammar-patches :as patches]))
(set! *warn-on-reflection* true)


;; Create parser from combined grammar file with runtime patches applied
(def lua-parser
  "ANTLR4 parser for Lua. Compiles grammar on first use.

   The original Lua.g4 grammar is kept unmodified from upstream
   (antlr/grammars-v4 repo). We apply runtime patches to fix issues
   without modifying the original file.

   See clua.parser.grammar-patches for details on what's patched and why."
  (antlr/parser
    (-> (io/resource "Lua.g4")
        slurp
        (str/replace "\r\n" "\n")
        patches/apply-patches)))

(defn parse
  "Parse Lua source code using ANTLR4.
   Returns parse tree structure."
  [source]
  (lua-parser source))

(defn parse-and-transform
  "Parse and transform to CLua AST format."
  [source]
  (transform/transform (parse source)))
