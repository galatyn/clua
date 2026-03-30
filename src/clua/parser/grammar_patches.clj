(ns clua.parser.grammar-patches
  "Runtime patches for the upstream Lua.g4 grammar.

   We keep the original Lua.g4 unmodified so we can:
   - Easily update from upstream (antlr/grammars-v4 repo)
   - Avoid licensing issues with redistributing modified grammars
   - Clearly document our changes and why they're needed

   Each patch includes:
   - Pattern to match (regex)
   - Replacement text
   - Comment explaining why the patch is needed"
  (:require [clojure.string :as str]))
(set! *warn-on-reflection* true)


;; =============================================================================
;; Patch: Block Comment Handling
;; =============================================================================

(def block-comment-fix
  "Fix for block comments being consumed by line comments.

   PROBLEM:
   The upstream COMMENT rule uses alternation with a greedy line comment pattern:
     COMMENT: '--' ( '[' NESTED_STR ']' | ~[\\r\\n]* ) -> channel(HIDDEN);

   The second alternative (~[\\r\\n]*) is greedy and matches ALL characters until
   end of line, including block comment delimiters. Since ANTLR lexers choose the
   longest match, LINE_COMMENT wins over BLOCK_COMMENT, causing code after block
   comments on the same line to be treated as part of the comment.

   Example that fails with original grammar:
     x = 10 --[[ comment ]] print(x)
     --^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  All treated as comment, print(x) lost!

   SOLUTION:
   Split into separate lexer rules with explicit precedence:
   1. BLOCK_COMMENT: Matches --[[...]] (level 0)
   2. BLOCK_COMMENT_EQ: Matches --[=[...]=] (with equals)
   3. LINE_COMMENT: Explicitly avoids --[[ and --[= patterns

   The LINE_COMMENT pattern uses a careful construction:
     '--' ((~[[\r\n] ~[\r\n]*)? | '[' '='* ~[[=\r\n] ~[\r\n]* | '[' '='*)

   This means:
   - Alt 1: '--' optionally followed by not-'['/not-newline, then rest-of-line
            The ? makes the whole group optional so '--' alone (empty comment) works.
            Using ~[[\r\n] (not '[', not newline) prevents consuming past line endings.
   - Alt 2: '--[=*' followed by not-'[' and not-'=', then anything until EOL
   - Alt 3: '--[=*' at end-of-line (bare bracket/equals at EOL, e.g. --[ or --[=)

   Alts 2 and 3 prevent LINE_COMMENT from matching block comment starts (--[[ or --[=[),
   while allowing --[ or --[= at EOL to be valid line comments (fixes nextvar.lua).

   Upstream issue: This appears to be a known limitation of the grammars-v4
   Lua grammar that affects single-line block comments."

  {:pattern #"COMMENT: '--' \( '\[' NESTED_STR '\]' \| ~\[\\r\\n\]\* \) -> channel\(HIDDEN\);"

   :replacement
   "// PATCHED: Split COMMENT rule to fix block comment handling (see grammar_patches.clj)
// Block comments must come BEFORE line comments to get priority
BLOCK_COMMENT: '--' '[' NESTED_STR ']' -> channel(HIDDEN);
LINE_COMMENT: '--' ((~[[\\\\r\\\\n] ~[\\\\r\\\\n]*)? | '[' '='* ~[[=\\\\r\\\\n] ~[\\\\r\\\\n]* | '[' '='*) -> channel(HIDDEN);"})

;; =============================================================================
;; Patch: \z escape consuming following whitespace (F10)
;; =============================================================================

(def escape-seq-patch
  "Fix \\z escape to consume all following whitespace including newlines.

   PROBLEM:
   The upstream EscapeSequence fragment includes 'z' in the character class
   '[abfnrtvz\"'|$#\\\\]', so \\z is matched but the whitespace/newlines after
   it are left in the token stream as raw characters. When NORMALSTRING/CHARSTRING
   later exclude raw newlines (see string-newline-patch), a string like
   \"abc\\z\\n   def\" would fail to tokenize.

   SOLUTION:
   Remove 'z' from the general character class and add an explicit alternative
   '\\\\' 'z' [ \\t\\f\\r\\n\\u000B]* that greedily consumes all following whitespace.

   This matches Lua 5.3 spec: \\z skips the following whitespace sequence."

  {:pattern
   "fragment EscapeSequence:
    '\\\\' [abfnrtvz\"'|$#\\\\]
    | '\\\\' '\\r'? '\\n'
    | DecimalEscape
    | HexEscape
    | UtfEscape
;"

   :replacement
   "// PATCHED: \\z now consumes following whitespace/newlines (see grammar_patches.clj)
fragment EscapeSequence:
    '\\\\' [abfnrtv\"'|$#\\\\]
    | '\\\\' 'z' [ \\t\\f\\r\\n\\u000B]*
    | '\\\\' '\\r'? '\\n'
    | DecimalEscape
    | HexEscape
    | UtfEscape
;"})

;; =============================================================================
;; Patch: Reject literal newlines in short string literals (F8)
;; =============================================================================

(def string-newline-patch
  "Reject short string literals that contain unescaped newlines.

   PROBLEM:
   The upstream NORMALSTRING/CHARSTRING rules use ~('\\\\' | '\"') and
   ~('\\\\' | '\\'\\'') respectively, which accept ANY character except the
   delimiter and backslash — including literal newlines. Lua 5.3 forbids
   literal newlines inside short strings (they must use \\n or \\z+newline).

   SOLUTION:
   Add '\\r' and '\\n' to the negated character sets so unescaped newlines
   terminate tokenization, causing a lex error — which becomes a load() failure.

   Note: escaped newlines ('\\\\' '\\r'? '\\n') and \\z+whitespace are still
   allowed because they are matched by EscapeSequence before the raw-char
   alternative is tried."

  {:pattern
   "NORMALSTRING: '\"' ( EscapeSequence | ~('\\\\' | '\"'))* '\"';

CHARSTRING: '\\'' ( EscapeSequence | ~('\\'' | '\\\\'))* '\\'';"

   :replacement
   "// PATCHED: reject literal newlines in short strings (see grammar_patches.clj)
NORMALSTRING: '\"' ( EscapeSequence | ~('\\\\' | '\"' | '\\r' | '\\n'))* '\"';

CHARSTRING: '\\'' ( EscapeSequence | ~('\\'' | '\\\\' | '\\r' | '\\n'))* '\\'';"})

;; =============================================================================
;; Patch: Lua 5.5 'global' declaration statement
;; =============================================================================

(def global-statement-patch
  "Add Lua 5.5 'global' keyword and declaration statement forms.

   PROBLEM:
   Lua 5.5 introduces a 'global' declaration statement:
     global function f(x) ... end   -- same as: function f(x) ... end
     global <const> x, y = 1, 2    -- global with attribute
     global x = value               -- global assignment
     global none                    -- declare no globals (no-op)
     global <const> *               -- wildcard (no-op)
   The original Lua.g4 does not include this syntax.

   SOLUTION:
   1. Add GLOBAL lexer token before NAME so 'global' is not treated as a NAME.
   2. Add globalnamelist parser rule (name list or '*' wildcard).
   3. Add two new stat alternatives:
      - global function funcname funcbody
      - global [<attrib>] globalnamelist [= explist]
   Semantics are handled in antlr_transform.clj: global function maps to
   func-stat; global name=value maps to assignment; bare declarations are no-ops."

  [{:pattern "NAME: [a-zA-Z_][a-zA-Z_0-9]*;"
    :replacement "GLOBAL   : 'global';\nNAME: [a-zA-Z_][a-zA-Z_0-9]*;"}

   {:pattern "    | 'local' attnamelist ('=' explist)?\n    ;"
    :replacement (str "    | 'local' attnamelist ('=' explist)?\n"
                      "    | 'global' 'function' funcname funcbody\n"
                      "    | 'global' ('<' NAME '>')? globalnamelist ('=' explist)?\n"
                      "    ;\n\n"
                      "globalnamelist\n"
                      "    : NAME ('<' NAME '>')? (',' NAME ('<' NAME '>')?)*\n"
                      "    | '*'\n"
                      "    ;")}])

;; =============================================================================
;; Patch: Attribute-before-name in local declarations (Lua 5.5)
;; =============================================================================

(def attrib-before-name-patch
  "Support 'local <attrib>name' syntax in addition to 'local name <attrib>'.

   PROBLEM:
   The Lua 5.5 test suite uses 'local <close>var = ...' (attribute before name,
   no space) in addition to the standard 'local var <close> = ...' ordering.
   The upstream attnamelist rule only supports NAME-first order.

   SOLUTION:
   Replace the attnamelist rule to accept either ordering per entry:
     (attrib NAME | NAME attrib)
   This handles both 'local <close>x' and 'local x <close>' forms."

  {:pattern "attnamelist\n    : NAME attrib (',' NAME attrib)*\n    ;"
   :replacement
   (str "attnamelist\n"
        "    : attribname (',' attribname)*\n"
        "    ;\n\n"
        "attribname\n"
        "    : attrib NAME attrib\n"
        "    | attrib NAME\n"
        "    | NAME attrib\n"
        "    ;")})

;; =============================================================================
;; Patch Application
;; =============================================================================

(defn apply-patches
  "Apply all grammar patches to the source.

   Patches are applied in order. Each patch is a map with:
   - :pattern - string or regex to match the original text
   - :replacement - replacement text

   Returns the patched grammar source as a string."
  [grammar-source]
  (-> grammar-source
      (str/replace (:pattern block-comment-fix)
                   (:replacement block-comment-fix))
      (str/replace (:pattern escape-seq-patch)
                   (:replacement escape-seq-patch))
      (str/replace (:pattern string-newline-patch)
                   (:replacement string-newline-patch))
      (str/replace (:pattern (first global-statement-patch))
                   (:replacement (first global-statement-patch)))
      (str/replace (:pattern (second global-statement-patch))
                   (:replacement (second global-statement-patch)))
      (str/replace (:pattern attrib-before-name-patch)
                   (:replacement attrib-before-name-patch))))
