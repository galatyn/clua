(ns clua.parser.antlr-transform
  "Transforms ANTLR parse trees to CLua AST format (matching Instaparse output).")
(set! *warn-on-reflection* true)


(declare transform)

(def ^:dynamic *source*
  "The source string being transformed. Bound by parser.clj during parse-and-transform
   to enable accurate operator line tracking in binary/unary expressions."
  nil)

(defn- find-op-row
  "Scan source between char indices start (inclusive) and end (exclusive) for the
   first non-whitespace character.  Returns its 0-indexed row (line number), or nil
   if none is found or *source* is absent."
  [^long start ^long end]
  (when-let [^String src *source*]
    (let [src-len (.length src)]
      (loop [i start]
        (when (and (< i end) (< i src-len))
          (let [ch (.charAt src i)]
            (if (or (= ch \space) (= ch \tab) (= ch \newline) (= ch \return))
              (recur (inc i))
              ;; Count newlines from the beginning of source up to index i
              (loop [j (long 0) n (long 0)]
                (if (>= j i)
                  n
                  (recur (unchecked-inc j)
                         (if (= (.charAt src j) \newline) (unchecked-inc n) n)))))))))))

(defn- filter-tokens
  "Remove string tokens (keywords, operators) from ANTLR tree, keeping only semantic nodes.
   Keep literal keywords: nil, true, false."
  [nodes]
  (filter #(or (and (string? %) (#{"nil" "true" "false" "..."} %))
               (and (not (string? %)) (not= % "<EOF>"))) nodes))

(defn- first-child [node]
  (when (seq? node)
    (second node)))

(defn- children [node]
  (when (seq? node)
    (rest node)))

(defn- tag [node]
  (when (seq? node)
    (first node)))

(defn- extract-position
  "Extract position metadata from ANTLR node and convert to CLua format.
   ANTLR uses 0-indexed rows/columns, CLua uses 1-indexed line/column."
  [node]
  (when-let [pos (get (meta node) :clj-antlr/position)]
    {:line (unchecked-inc (long (:row pos)))
     :column (unchecked-inc (long (:column pos)))}))

(defn- with-position
  "Attach position metadata to a transformed node."
  [new-node source-node]
  (if-let [pos (extract-position source-node)]
    (with-meta new-node pos)
    new-node))

(defn- transform-number [node]
  (let [num-str (first (filter string? (children node)))]
    (cond
      ;; Check for hex integers
      (re-matches #"0[xX][0-9a-fA-F]+" num-str)
      [:Numeral [:HexInteger num-str]]

      ;; Check for floats (contains . or e/E)
      (or (re-find #"\." num-str) (re-find #"[eE]" num-str))
      [:Numeral [:Float num-str]]

      ;; Regular integer
      :else
      [:Numeral [:Integer num-str]])))

(defn- transform-string [node]
  (let [str-val (first (filter string? (children node)))]
    [:LiteralString [:ShortString str-val]]))

(defn- wrap-in-precedence
  "Wrap a primary expression in all the precedence layers."
  [primary]
  [:exp
   [:or-exp
    [:and-exp
     [:cmp-exp
      [:bitor-exp
       [:bitxor-exp
        [:bitand-exp
         [:shift-exp
          [:concat-exp
           [:add-exp
            [:mul-exp
             [:unary-exp
              [:power-exp
               [:primary-exp primary]]]]]]]]]]]]]])

(defn- transform-exp
  "Transform an expression node."
  [node]
  (let [all-children (children node)
        strings (filter string? all-children)
        nodes (filter seq? all-children)]
    (cond
      ;; Binary operator: exp op exp
      (and (= 2 (count nodes)) (= 1 (count strings)))
      (let [op (first strings)
            [left right] nodes
            ;; Operator is the first non-whitespace char between left.stop+1 and right.index
            left-stop (-> left meta :clj-antlr/position :stop)
            right-idx (-> right meta :clj-antlr/position :index)
            op-row (when (and (some? left-stop) (some? right-idx))
                     (find-op-row (inc (long left-stop)) (long right-idx)))
            result [:add-exp (transform left) op (transform right)]]
        (if (some? op-row)
          (with-meta result {:op-line (unchecked-inc (long op-row))}) ; 0-indexed row → 1-indexed line
          result))

      ;; Unary operator: op exp
      ;; The outer :exp node's position IS the operator's position (operator is first token)
      (and (= 1 (count nodes)) (= 1 (count strings)))
      (let [op (first strings)
            operand (first nodes)
            op-pos (extract-position node)
            result [:unary-exp op (transform operand)]]
        (if-let [op-line (:line op-pos)]
          (with-meta result {:op-line op-line})
          result))

      ;; Single child: just wrap in precedence layers
      (and (= 1 (count nodes)) (empty? strings))
      (let [child (first nodes)]
        (cond
          (= (tag child) :number)
          (wrap-in-precedence (transform-number child))

          (= (tag child) :string)
          (wrap-in-precedence (transform-string child))

          :else
          (wrap-in-precedence (transform child))))

      ;; Literal keywords
      (and (= 1 (count strings)) (empty? nodes) (#{"nil" "true" "false"} (first strings)))
      (wrap-in-precedence [(keyword (str (first strings) "-lit"))])

      ;; Vararg: ...
      (and (= 1 (count strings)) (empty? nodes) (= "..." (first strings)))
      (wrap-in-precedence {:type :vararg})

      :else
      (wrap-in-precedence (transform (first nodes))))))

(defn- transform-var
  "Transform a variable reference, which may include indexing or field access."
  [node]
  (let [all-children (children node)
        strings (filter string? all-children)
        nodes (filter seq? all-children)]
    (cond
      ;; Simple variable: just a name
      (and (= 1 (count strings)) (empty? nodes))
      (with-position [:varref [:Name (first strings)]] node)

      ;; Bracket indexing: var[exp]
      (and (some #(= "[" %) strings) (some #(= "]" %) strings))
      (let [;; Find the base (prefixexp or name before bracket)
            prefixexp (first (filter #(= (tag %) :prefixexp) nodes))
            base-name (first strings)
            ;; Find the index expression
            index-exp (first (filter #(= (tag %) :exp) nodes))
            base (if prefixexp
                   (transform prefixexp)
                   [:varref [:Name base-name]])]
        [:prefixexp base [:indexsuffix (transform index-exp)]])

      ;; Field access: var.field  (e.g., a.b)
      ;; Structure: (:var (:prefixexp "a") "." "b")
      (some #(= "." %) strings)
      (let [prefixexp (first (filter #(= (tag %) :prefixexp) nodes))
            field-name (last strings)]                      ; The field name comes after "."
        (if prefixexp
          [:prefixexp (transform prefixexp) [:fieldsuffix [:Name field-name]]]
          ;; Shouldn't happen, but fallback
          [:varref [:Name (first strings)]]))

      ;; Has a prefixexp child - use it
      (seq nodes)
      (transform (first nodes))

      ;; Fallback
      :else
      [:varref [:Name (first strings)]])))

(defn- transform-varlist [node]
  (let [vars (filter #(= (tag %) :var) (children node))]
    (map transform-var vars)))

(defn- transform-explist [node]
  (let [exps (filter #(= (tag %) :exp) (children node))
        result (into [:explist] (map transform exps))]
    (with-position result node)))

(defn- transform-args
  "Transform function arguments.
   Handles three cases:
   1. (args (explist ...)) - normal function call with parentheses
   2. (args (string ...)) - string literal without parentheses: f\"str\"
   3. (args (tableconstructor ...)) - table constructor without parentheses: f{...}"
  [node]
  (let [explist (first (filter #(= (tag %) :explist) (children node)))
        string-node (first (filter #(= (tag %) :string) (children node)))
        table-node (first (filter #(= (tag %) :tableconstructor) (children node)))
        transformed-explist (when explist (transform explist))]
    (when (and transformed-explist (> (- (count transformed-explist) 1) 255))
      (throw (ex-info "too many registers" {:type :parse-error})))
    [:args
     (cond
       transformed-explist transformed-explist
       string-node [:explist (transform string-node)]
       table-node [:explist (transform table-node)]
       :else [:explist])]))

(defn- transform-prefixexp
  "Transform a prefix expression (variable reference, function call, or parenthesized exp).
   Handles mixed field access (.) and bracket indexing ([]) in order."
  [node]
  (let [all-children (children node)
        strings (filter string? all-children)
        nodes (filter seq? all-children)]
    (cond
      ;; Simple name reference
      (and (= 1 (count strings)) (empty? nodes))
      (with-position [:varref [:Name (first strings)]] node)

      ;; Single node child (function call or nested exp) - pass through
      (and (= 1 (count nodes)) (empty? strings))
      (transform (first nodes))

      ;; Parenthesized expression: (exp)
      ;; ANTLR gives: (:prefixexp "(" (:exp ...) ")")
      ;; In Lua, (expr) truncates multiple values to one. Emit :paren-exp to track this.
      (and (= 1 (count nodes))
           (= 2 (count strings))
           (= "(" (first strings))
           (= ")" (second strings)))
      [:paren-exp (transform (first nodes))]

      ;; Mixed field/bracket access or just fields or just brackets
      ;; Parse all suffixes in order: data.values[1].name[2]
      (or (some #(= "." %) strings) (some #(= "[" %) strings))
      (let [;; Parse base and all suffixes in order
            parse-suffixes (fn [children]
                             (loop [remaining children
                                    base nil
                                    suffixes []]
                               (if (empty? remaining)
                                 [base suffixes]
                                 (let [elem (first remaining)]
                                   (cond
                                     ;; Found "[" - bracket index suffix
                                     (= elem "[")
                                     (let [exp-node (second remaining)
                                           after-exp (drop 2 remaining)]
                                       (if (and (= "]" (first after-exp))
                                                (= (tag exp-node) :exp))
                                         (recur (rest after-exp) base
                                                (conj suffixes [:index exp-node]))
                                         (recur (rest remaining) base suffixes)))

                                     ;; Found "." - field suffix
                                     (= elem ".")
                                     (let [field-name (second remaining)]
                                       (if (string? field-name)
                                         (recur (drop 2 remaining) base
                                                (conj suffixes [:field field-name]))
                                         (recur (rest remaining) base suffixes)))

                                     ;; Skip "]" (already handled)
                                     (= elem "]")
                                     (recur (rest remaining) base suffixes)

                                     ;; Parenthesized base: (expr) with following suffixes
                                     ;; e.g. ({f()})[1] → "(" exp ")" "[" exp "]"
                                     (and (= elem "(") (nil? base))
                                     (let [inner-node (second remaining)]
                                       (if (and inner-node (seq? inner-node))
                                         (recur (drop 3 remaining)
                                                [:paren-exp (transform inner-node)]
                                                suffixes)
                                         (recur (rest remaining) elem suffixes)))

                                     ;; Before any suffix - this is the base
                                     (nil? base)
                                     (recur (rest remaining) elem suffixes)

                                     ;; Everything else - skip
                                     :else
                                     (recur (rest remaining) base suffixes))))))
            [base-elem suffix-list] (parse-suffixes all-children)
            ;; Transform the base
            base (cond
                   (string? base-elem) [:varref [:Name base-elem]]
                   (seq? base-elem) (transform base-elem)
                   (vector? base-elem) base-elem            ; already-transformed node (e.g. [:paren-exp ...])
                   :else [:varref [:Name "unknown"]])
            ;; Apply all suffixes in order
            result (reduce (fn [acc [suffix-type suffix-val]]
                             (case suffix-type
                               :field [:prefixexp acc [:fieldsuffix [:Name suffix-val]]]
                               :index [:prefixexp acc [:indexsuffix (transform suffix-val)]]))
                           base
                           suffix-list)]
        result)

      ;; Multiple parts - wrap in prefixexp
      :else
      [:prefixexp (vec (map transform (filter-tokens all-children)))])))

(defn- transform-functioncall
  "Transform a function call from ANTLR format.

   Parses ANTLR children sequentially to handle all call chain patterns:
   - f(args)                      → simple call
   - f(a).g(b)                    → chained call with field access
   - f(a):g(b)                    → chained call with method
   - obj:m(args)                  → method call
   - table.f(args)                → dotted field call
   - require('debug').getinfo(1)  → multi-step dotted call
   - f()()                        → chained calls
   - (exp)(args)                  → parenthesized base call
   - (exp):m(args)                → parenthesized base method call

   ANTLR flattens all children: base [suffix|call]* so we scan left-to-right
   building up the expression rather than filtering by type.

   Attaches ANTLR position to the result so call sites can update currentline."
  [node]
  (let [result
        (loop [remaining (children node)
               acc nil]
          (if (empty? remaining)
            (or acc [:functioncall [:varref [:Name "?"]] [:args]])
            (let [elem (first remaining)]
              (cond
                ;; Initial base: NAME string (not an operator)
                (and (nil? acc)
                     (string? elem)
                     (not (#{"(" "." ":" "[" "]"} elem)))
                (recur (rest remaining) [:varref [:Name elem]])

                ;; Initial base: "(" exp ")" — parenthesized expression
                (and (nil? acc) (= "(" elem))
                (let [exp-node (second remaining)
                      after-paren (drop 2 remaining)]       ; drop "(" and exp-node
                  (if (and (seq? exp-node) (= (tag exp-node) :exp))
                    (recur (rest after-paren)               ; drop ")"
                           (transform exp-node))
                    (recur (rest remaining) acc)))

                ;; (:args ...) node → function call on current accumulator
                (and acc (seq? elem) (= (tag elem) :args))
                (recur (rest remaining)
                       [:functioncall acc (transform elem)])

                ;; "." followed by field name → field access
                (and acc (= "." elem) (string? (second remaining)))
                (recur (drop 2 remaining)
                       [:prefixexp acc [:fieldsuffix [:Name (second remaining)]]])

                ;; "[" exp "]" → index access
                (and acc (= "[" elem) (seq? (second remaining)))
                (recur (drop 3 remaining)                   ; drop "[", exp, "]"
                       [:prefixexp acc [:indexsuffix (transform (second remaining))]])

                ;; ":" method-name (:args ...) → method call
                (and acc (= ":" elem)
                     (string? (second remaining))
                     (seq? (nth remaining 2 nil)))
                (recur (drop 3 remaining)                   ; drop ":", method-name, args
                       [:methodcall acc [:Name (second remaining)]
                        (transform (nth remaining 2))])

                ;; Skip unrecognized tokens (e.g. stray ")")
                :else
                (recur (rest remaining) acc)))))]
    (with-position result node)))


(defn- extract-attrib-name
  "Extract attrib name string from an :attrib node, or nil if absent."
  [attrib-node]
  (when (and attrib-node (> (count (children attrib-node)) 1))
    (second (children attrib-node))))

(defn- extract-attnamelist
  "Extract (name, attrib) pairs from an ANTLR :attnamelist node.
   With the attrib-before-name grammar patch, children are :attribname nodes
   (each wrapping 'attrib NAME attrib', 'attrib NAME', or 'NAME attrib') separated by commas.

   Prefix-applies-to-all: when the first attribname has a non-empty prefix attrib
   (attrib before NAME, i.e. 'local <close> a, b'), that attrib is propagated to all
   subsequent entries that have no explicit attrib of their own.  This matches Lua 5.5
   semantics where 'local <close> a, b' makes both a and b to-be-closed.

   Returns a vector of {:name str :attrib str-or-nil}."
  [attnamelist-node]
  (let [entries
        (reduce (fn [result item]
                  (cond
                    ;; New grammar: each entry is an :attribname node
                    (and (seq? item) (= (tag item) :attribname))
                    (let [ch (children item)
                          first-ch (first ch)
                          second-ch (second ch)]
                      (cond
                        ;; attrib NAME [attrib] order: first child is :attrib node.
                        ;; Covers 'attrib NAME' and 'attrib NAME attrib' (double-attribute).
                        ;; Use whichever attrib is non-empty (prefix takes precedence).
                        (and (seq? first-ch) (= (tag first-ch) :attrib))
                        (let [third-ch (nth ch 2 nil)
                              suffix (when (and (seq? third-ch) (= (tag third-ch) :attrib)) third-ch)
                              prefix-a (extract-attrib-name first-ch)
                              effective (or prefix-a (extract-attrib-name suffix))]
                          (conj result {:name second-ch :attrib effective :prefix? (some? prefix-a)}))
                        ;; NAME attrib order: first child is a string (name)
                        (string? first-ch)
                        (let [attrib-node (when (and (seq? second-ch) (= (tag second-ch) :attrib)) second-ch)]
                          (conj result {:name first-ch :attrib (extract-attrib-name attrib-node) :prefix? false}))
                        :else result))
                    :else result))
                []
                (children attnamelist-node))
        ;; If the first entry has a non-empty prefix attrib, propagate it to
        ;; all subsequent entries that have no explicit attrib of their own.
        list-attrib (when (and (seq entries) (:prefix? (first entries)) (:attrib (first entries)))
                      (:attrib (first entries)))]
    (if list-attrib
      (mapv (fn [e] (if (:attrib e) e (assoc e :attrib list-attrib))) entries)
      entries)))

(defn- char-index->row
  "Count newlines in *source* from position 0 up to char-index.
   Returns the 0-indexed row number, or nil if *source* is absent."
  [^long char-index]
  (when-let [^String src *source*]
    (let [limit (min char-index (.length src))]
      (loop [i (long 0) n (long 0)]
        (if (>= i limit)
          n
          (recur (unchecked-inc i) (if (= (.charAt src i) \newline) (unchecked-inc n) n)))))))

(defn- transform-stat [node]
  (let [child-nodes (filter-tokens (children node))
        end-line (let [raw-pos (get (meta node) :clj-antlr/position)
                       stop-idx (when raw-pos (:stop raw-pos))]
                   (when stop-idx (some-> (char-index->row (long stop-idx)) (as-> r (unchecked-inc (long r))))))
        result (cond
                 ;; Local function: local function Name funcbody (check before local assignment)
                 (and (some #(= % "local") (children node))
                      (some #(= % "function") (children node)))
                 (let [all-children (children node)
                       strings (filter string? all-children)
                       func-name (nth strings 2)
                       funcbody (first (filter #(= (tag %) :funcbody) child-nodes))]
                   [:stat [:local-func-stat [:Name func-name] (transform funcbody)]])

                 ;; Local assignment: local attnamelist = explist
                 (some #(= % "local") (children node))
                 (let [attnamelist (first (filter #(= (tag %) :attnamelist) child-nodes))
                       explist (first (filter #(= (tag %) :explist) child-nodes))
                       name-attrs (extract-attnamelist attnamelist)]
                   [:stat
                    [:local-stat
                     (into [:namelist] (for [{:keys [name attrib]} name-attrs]
                                         (if attrib [:NameAttr name attrib] [:Name name])))
                     (if explist (transform explist) [:explist])]])

                 ;; Return statement
                 (some #(= % "return") (children node))
                 (let [explist (first (filter #(= (tag %) :explist) child-nodes))]
                   [:stat [:retstat (if explist (transform explist) [:explist])]])

                 ;; Function call
                 (= (tag (first child-nodes)) :functioncall)
                 [:stat (transform (first child-nodes))]

                 ;; If statement: if exp then block (elseif exp then block)* (else block)? end
                 (some #(= % "if") (children node))
                 (let [exps (filter #(= (tag %) :exp) child-nodes)
                       blocks (filter #(= (tag %) :block) child-nodes)
                       n-exps (count exps)
                       n-blocks (count blocks)
                       has-else (> n-blocks n-exps)
                       elseif-exps (rest exps)
                       elseif-blocks (if has-else (butlast (rest blocks)) (rest blocks))
                       elseif-clauses (mapv (fn [e b] [:elseif-clause (transform e) (transform b)])
                                            elseif-exps elseif-blocks)
                       else-clause (when has-else [[:else-clause (transform (last blocks))]])]
                   [:stat (cond-> (vec (concat [:if-stat
                                               (transform (first exps))
                                               (transform (first blocks))]
                                              elseif-clauses
                                              (or else-clause [])))
                            end-line (with-meta {:end-line end-line}))])

                 ;; While loop: while exp do block end
                 (some #(= % "while") (children node))
                 (let [exp (first (filter #(= (tag %) :exp) child-nodes))
                       block (first (filter #(= (tag %) :block) child-nodes))]
                   [:stat (cond-> [:while-stat (transform exp) (transform block)]
                            end-line (with-meta {:end-line end-line}))])

                 ;; For numeric: for Name = exp, exp [, exp] do block end
                 (and (some #(= % "for") (children node))
                      (not (some #(= % "in") (children node))))
                 (let [all-children (children node)
                       strings (filter string? all-children)
                       var-name (second strings)
                       exps (filter #(= (tag %) :exp) child-nodes)
                       block (first (filter #(= (tag %) :block) child-nodes))]
                   (case (count exps)
                     2 [:stat (cond-> [:for-numeric [:Name var-name] (transform (first exps)) (transform (second exps)) (transform block)]
                                end-line (with-meta {:end-line end-line}))]
                     3 [:stat (cond-> [:for-numeric [:Name var-name] (transform (first exps)) (transform (second exps)) (transform (nth exps 2)) (transform block)]
                                end-line (with-meta {:end-line end-line}))]
                     [:stat (vec (map transform child-nodes))]))

                 ;; For generic: for namelist in explist do block end
                 (and (some #(= % "for") (children node))
                      (some #(= % "in") (children node)))
                 (let [namelist (first (filter #(= (tag %) :namelist) child-nodes))
                       explist (first (filter #(= (tag %) :explist) child-nodes))
                       block (first (filter #(= (tag %) :block) child-nodes))]
                   [:stat (cond-> [:for-generic (transform namelist) (transform explist) (transform block)]
                            end-line (with-meta {:end-line end-line}))])

                 ;; Repeat: repeat block until exp
                 (some #(= % "repeat") (children node))
                 (let [block (first (filter #(= (tag %) :block) child-nodes))
                       exp (first (filter #(= (tag %) :exp) child-nodes))]
                   [:stat [:repeat-stat (transform block) (transform exp)]])

                 ;; Label statement: ::name::
                 (and (= 1 (count child-nodes))
                      (= :label (tag (first child-nodes))))
                 (let [label-node (first child-nodes)
                       label-name (first (filter #(not= "::" %) (filter string? (children label-node))))]
                   [:stat [:label [:Name label-name]]])

                 ;; Goto: goto Name
                 (some #(= % "goto") (children node))
                 (let [label-name (first (filter string? (filter #(not= "goto" %) (children node))))]
                   [:stat [:goto-stat [:Name label-name]]])

                 ;; Global function (Lua 5.5): global function funcname funcbody
                 ;; Different from plain 'function' — declares the name as a global reference
                 ;; in the current scope so that the assignment targets the global environment,
                 ;; not any shadowing local variable.
                 (and (some #(= % "global") (children node))
                      (some #(= % "function") (children node)))
                 (let [funcname (first (filter #(= (tag %) :funcname) child-nodes))
                       funcbody (first (filter #(= (tag %) :funcbody) child-nodes))]
                   [:stat [:global-func-stat (transform funcname) (transform funcbody)]])

                 ;; Global declaration (Lua 5.5): global [<attrib>] namelist [= explist]
                 ;; Two attrib positions are supported:
                 ;;   Prefix: global<const> name1, name2  — attrib is direct child of stat
                 ;;   Per-name: global name<const>         — attrib follows each name in globalnamelist
                 (some #(= % "global") (children node))
                 (let [all-children (children node)
                       stat-strings (set (filter string? all-children))
                       ;; Prefix attrib: '<' attrib '>' as direct children of the stat node
                       prefix-attrib (when (and (contains? stat-strings "<") (contains? stat-strings ">"))
                                       (second (drop-while #(not= "<" %) all-children)))
                       globalnamelist (first (filter #(= (tag %) :globalnamelist) child-nodes))
                       explist (first (filter #(= (tag %) :explist) child-nodes))
                       ;; Parse globalnamelist: Name [< attrib >] (, Name [< attrib >])*
                       name-attrib-pairs
                       (when globalnamelist
                         (loop [cs (filter string? (children globalnamelist))
                                acc []]
                           (cond
                             (empty? cs) acc
                             (= (first cs) ",") (recur (rest cs) acc)
                             ;; Name possibly followed by <attrib>
                             :else
                             (let [n (first cs)
                                   after (rest cs)]
                               (if (= (first after) "<")
                                 (let [attrib (second after)]
                                   (recur (drop 3 after) (conj acc [n attrib])))
                                 (recur after (conj acc [n nil])))))))
                       names (map first name-attrib-pairs)]
                   (cond
                     (= (vec names) ["none"])
                     [:stat [:global-none]]

                     (= (vec names) ["*"])
                     [:stat (if prefix-attrib [:global-wildcard prefix-attrib] [:global-wildcard])]

                     (seq names)
                     (let [namelist (into [:namelist]
                                          (for [[n per-attrib] name-attrib-pairs]
                                            (let [a (or per-attrib prefix-attrib)]
                                              (if a [:NameAttr n a] [:Name n]))))]
                       [:stat (if explist
                                [:global-decl namelist (transform explist)]
                                [:global-decl namelist])])

                     :else
                     [:stat [:nop]]))

                 ;; Function definition: function funcname funcbody
                 (some #(= % "function") (children node))
                 (let [funcname (first (filter #(= (tag %) :funcname) child-nodes))
                       funcbody (first (filter #(= (tag %) :funcbody) child-nodes))]
                   [:stat [:func-stat (transform funcname) (transform funcbody)]])

                 ;; Break statement
                 (some #(= % "break") (children node))
                 [:stat [:break-stat]]

                 ;; Do block: do block end (sole filtered child is the :block)
                 (and (= 1 (count child-nodes))
                      (= :block (tag (first child-nodes))))
                 (let [block (first child-nodes)]
                   [:stat [:do-stat (transform block)]])

                 ;; Assignment: varlist '=' explist (must check after control flow statements)
                 (some #(= % "=") (children node))
                 (let [varlist (first (filter #(= (tag %) :varlist) child-nodes))
                       explist (first (filter #(= (tag %) :explist) child-nodes))]
                   [:stat
                    (into [:assignment] (concat (transform-varlist varlist)
                                                [(transform explist)]))])

                 ;; Other statements - fallback
                 :else
                 [:stat (vec (map transform child-nodes))])]
    (with-position result node)))

(defn- transform-field
  "Transform a table field (named field or array field)."
  [node]
  (let [all-children (children node)
        strings (filter string? all-children)
        nodes (filter seq? all-children)
        exps (filter #(= (tag %) :exp) nodes)]
    (cond
      ;; Bracketed field: [key-exp] = value-exp (check before named field!)
      ;; Format expected by parser.clj: ["[" key-exp "]" value-exp]
      (some #(= "[" %) strings)
      (let [[key-exp value-exp] exps]
        [:field "[" (transform key-exp) "]" (transform value-exp)])

      ;; Named field: name = exp
      (some #(= "=" %) strings)
      (let [field-name (first strings)
            value-exp (first exps)]
        [:field [:Name field-name] (transform value-exp)])

      ;; Simple array field: just exp
      :else
      [:field (transform (first exps))])))

(defn- transform-fieldlist
  "Transform a fieldlist (comma-separated fields)."
  [node]
  (let [field-nodes (filter #(= (tag %) :field) (children node))]
    (into [:fieldlist] (map transform field-nodes))))

(defn- transform-tableconstructor
  "Transform a table constructor."
  [node]
  (let [fieldlist (first (filter #(= (tag %) :fieldlist) (children node)))]
    [:tableconstructor (if fieldlist (transform fieldlist) [:fieldlist []])]))

(defn- transform-funcname
  "Transform a function name (may be dotted like a.b.c or a.b:c)."
  [node]
  (let [all-children (children node)
        strings (filter string? all-children)]
    (cond
      ;; Method definition: a.b:method (has colon)
      (some #(= ":" %) strings)
      (let [parts (remove #{":" "."} strings)
            first-name (first parts)
            middle-parts (butlast (rest parts))
            method-name (last parts)]
        (into [:funcname [:Name first-name]]
              (concat (map (fn [n] [:dotname [:Name n]]) middle-parts)
                      [[:colonname [:Name method-name]]])))

      ;; Dotted function: a.b.c (has dots)
      (some #(= "." %) strings)
      (let [parts (remove #{"."} strings)
            first-name (first parts)
            rest-names (rest parts)]
        (into [:funcname [:Name first-name]]
              (map (fn [n] [:dotname [:Name n]]) rest-names)))

      ;; Simple function: foo
      :else
      [:funcname [:Name (first strings)]])))

(defn- transform-funcbody
  "Transform a function body: (parlist) block end.
   Attaches :line (start of '(') and :last-line (line of 'end') as metadata
   so the interpreter can populate linedefined/lastlinedefined."
  [node]
  (let [child-nodes (filter-tokens (children node))
        parlist (first (filter #(= (tag %) :parlist) child-nodes))
        block (first (filter #(= (tag %) :block) child-nodes))
        result [:funcbody
                (if parlist (transform parlist) [:parlist])
                (transform block)]
        raw-pos (get (meta node) :clj-antlr/position)
        start-line (when raw-pos (inc (long (:row raw-pos))))
        stop-idx (when raw-pos (:stop raw-pos))
        end-line (when stop-idx (some-> (char-index->row (long stop-idx)) (as-> r (unchecked-inc (long r)))))]
    (if (or start-line end-line)
      (with-meta result {:line start-line :last-line end-line})
      result)))

(defn- transform-parlist
  "Transform parameter list.
   Supports Lua 5.5 named vararg: 'function f(...t)' where t captures varargs as a table."
  [node]
  (let [all-children (children node)
        child-nodes (filter-tokens all-children)
        namelist (first (filter #(= (tag %) :namelist) child-nodes))
        ddd-idx (some (fn [[i c]] (when (= "..." c) i))
                      (map-indexed vector all-children))
        ;; NAME token immediately after '...' (if any) is the vararg table name
        vararg-name (when ddd-idx
                      (let [after (drop (unchecked-inc (long ddd-idx)) all-children)
                            tok (first (filter #(and (string? %)
                                                     (not= "," %)) after))]
                        tok))
        has-vararg (some? ddd-idx)
        vararg-node (when has-vararg
                      (if vararg-name
                        {:type :vararg :name vararg-name}
                        {:type :vararg}))]
    (cond
      ;; Has both namelist and vararg
      (and namelist has-vararg)
      [:parlist (transform namelist) vararg-node]

      ;; Just namelist
      namelist
      [:parlist (transform namelist)]

      ;; Just vararg (possibly named)
      has-vararg
      [:parlist [:namelist] vararg-node]

      ;; Empty params
      :else
      [:parlist [:namelist]])))

(defn- transform-namelist
  "Transform a name list."
  [node]
  (let [all-children (children node)
        strings (filter string? all-children)
        names (remove #(= "," %) strings)]
    (into [:namelist] (map (fn [n] [:Name n]) names))))

(defn- transform-retstat [node]
  (let [explist (first (filter #(= (tag %) :explist) (children node)))
        exp-count (when explist (count (filter #(= (tag %) :exp) (children explist))))]
    (when (and exp-count (> (long exp-count) 254))
      (throw (ex-info "too many returns" {:type :error})))
    (with-position [:retstat (if explist (transform explist) [:explist])] node)))

(defn- fix-chained-calls-raw
  "Fix ANTLR parser bug where chained function calls with non-empty args
   are misparsed as two separate statements.

   Works on RAW ANTLR nodes before transformation.

   Pattern: load(x)() gets parsed as:
     Statement 1: (:stat 'local' ... '=' (:explist (:exp (:prefixexp 'load'))))
     Statement 2: (:stat (:functioncall '(' (:exp (:prefixexp 'x')) ')' (:args '(' ')')))

   This function detects and merges them into:
     (:stat 'local' ... '=' (:explist (:exp (:prefixexp (:functioncall 'load' (:args ...) (:args ...))))))
  "
  [raw-stats]
  (loop [result []
         remaining raw-stats]
    (if (empty? remaining)
      result
      (let [stmt (first remaining)
            next-stmt (second remaining)]
        ;; Check if next statement is a misparsed functioncall (starts with "(")
        (if (and next-stmt
                 (seq? next-stmt)
                 (= (tag next-stmt) :stat)
                 (let [fc (first (filter #(and (seq? %) (= (tag %) :functioncall)) (children next-stmt)))]
                   (and fc
                        (= (second fc) "("))))              ; functioncall's first child is "("
          ;; Found misparsed pattern - need to merge
          (let [;; Get the misparsed functioncall from next statement
                ;; Structure: (:functioncall "(" (:exp (:prefixexp "x")) ")" (:args "(" ")"))
                misparsed-fc (first (filter #(and (seq? %) (= (tag %) :functioncall)) (children next-stmt)))
                fc-children (vec (children misparsed-fc))
                ;; fc-children is: ["(" (:exp ...) ")" (:args ...) ...]
                exp-in-parens (first (filter #(and (seq? %) (= (tag %) :exp)) fc-children))
                _args-from-second-call (filter #(and (seq? %) (= (tag %) :args)) fc-children)

                ;; Get the target from previous statement
                ;; Statement 1 structure: (:stat ... (:explist (:exp (:prefixexp "load"))))
                ;; or dotted: (:stat ... (:explist (:exp (:prefixexp "io" "." "open"))))
                prev-children (children stmt)
                prev-explist (first (filter #(and (seq? %) (= (tag %) :explist)) prev-children))
                prev-exp (when prev-explist
                           (first (filter #(and (seq? %) (= (tag %) :exp)) (children prev-explist))))
                prev-prefixexp (when prev-exp
                                 (first (filter #(and (seq? %) (= (tag %) :prefixexp)) (children prev-exp))))
                ;; All children of prev-prefixexp, e.g., ["load"] or ["io" "." "open"]
                prefixexp-children (when prev-prefixexp (vec (children prev-prefixexp)))

                ;; Everything after ")" in the misparsed-fc is the rest of the call chain.
                ;; For (otherfile):lines(), fc-children = ["(" exp ")" ":" "lines" (:args)]
                ;; after-paren = [":" "lines" (:args)]  (used as additional chained calls)
                after-paren (when (seq fc-children)
                              (rest (drop-while #(not= % ")") fc-children)))

                ;; Build the proper chained functioncall
                ;; (:functioncall "io" "." "open" (:args "(" (:explist exp-in-parens) ")") ":" "lines" (:args))
                proper-fc (when (and (seq prefixexp-children) exp-in-parens)
                            (concat (list :functioncall)
                                    prefixexp-children
                                    (list (list :args "(" (list :explist exp-in-parens) ")"))
                                    after-paren))

                ;; Reconstruct the first statement with the merged functioncall
                is-local (some #(= % "local") prev-children)
                has-assignment (some #(= % "=") prev-children)

                fixed-stmt (when proper-fc
                             (cond
                               ;; Local assignment: replace the explist
                               is-local
                               (let [before-eq (take-while #(not= % "=") prev-children)]
                                 (concat (list :stat) before-eq (list "=") (list (list :explist (list :exp (list :prefixexp proper-fc))))))

                               ;; Regular assignment: replace the explist
                               has-assignment
                               (let [before-eq (take-while #(not= % "=") prev-children)]
                                 (concat (list :stat) before-eq (list "=") (list (list :explist (list :exp (list :prefixexp proper-fc))))))

                               ;; Expression statement
                               :else
                               (list :stat proper-fc)))]
            ;; Add the fixed statement (or keep originals if fix failed) and skip both
            (if fixed-stmt
              (recur (conj result fixed-stmt) (drop 2 remaining))
              ;; Fix failed - keep both statements
              (recur (conj result stmt) (rest remaining))))

          ;; Not a misparsed pattern - keep statement as is
          (recur (conj result stmt) (rest remaining)))))))

(defn- transform-block [node]
  (let [child-nodes (filter-tokens (children node))
        stats (filter #(= (tag %) :stat) child-nodes)
        retstat (first (filter #(= (tag %) :retstat) child-nodes))
        ;; Fix misparsed chained calls BEFORE transforming
        fixed-raw-stats (fix-chained-calls-raw stats)
        ;; Now transform the fixed statements
        transformed-stats (map transform fixed-raw-stats)]
    (into [:block]
          (concat transformed-stats
                  (when retstat [(transform retstat)])))))

(defn- transform-chunk [node]
  (let [block (first (filter #(= (tag %) :block) (children node)))]
    [:chunk (transform block)]))

(defn transform
  "Transform ANTLR parse tree to CLua AST format."
  [tree]
  (cond
    (not (seq? tree)) tree

    :else
    (let [node-tag (tag tree)]
      (case node-tag
        :start_ (transform (first-child tree))
        :chunk (transform-chunk tree)
        :block (transform-block tree)
        :stat (transform-stat tree)
        :retstat (transform-retstat tree)
        :exp (transform-exp tree)
        :explist (transform-explist tree)
        :prefixexp (transform-prefixexp tree)
        :functioncall (transform-functioncall tree)
        :var (transform-var tree)
        :args (transform-args tree)
        :number (transform-number tree)
        :string (transform-string tree)
        :tableconstructor (transform-tableconstructor tree)
        :fieldlist (transform-fieldlist tree)
        :field (transform-field tree)
        :funcname (transform-funcname tree)
        :funcbody (transform-funcbody tree)
        :parlist (transform-parlist tree)
        :namelist (transform-namelist tree)

        ;; Default: recursively transform children
        (into [(tag tree)] (map transform (filter-tokens (children tree))))))))
