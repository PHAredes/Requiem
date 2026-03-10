#!/usr/bin/env janet

(var ast/*debug-checks* false)

(defn ast/debug-checks? [] ast/*debug-checks*)
(defn ast/set-debug-checks! [enabled]
  (set ast/*debug-checks* enabled)
  ast/*debug-checks*)

(defn- ensure [pred value message]
  (when (and ast/*debug-checks* (not (pred value)))
    (errorf "%s: %v" message value)))

(defn- ensure-int>= [n lo message]
  (when ast/*debug-checks*
    (when (or (not (int? n)) (< n lo))
      (errorf "%s: %v" message n))))

(defn pos [line col offset]
  (ensure-int>= line 1 "pos.line >= 1")
  (ensure-int>= col 1 "pos.col >= 1")
  (ensure-int>= offset 0 "pos.offset >= 0")
  [:pos line col offset])

(defn span [start end]
  (ensure tuple? start "span.start tuple")
  (ensure tuple? end "span.end tuple")
  [:span start end])

(defn span/none []
  (let [p (pos 1 1 0)]
    (span p p)))

(defn ty/hole [name sp] [:ty/hole name sp])
(defn ty/universe [level sp]
  (ensure-int>= level 0 "ty/universe.level >= 0")
  [:ty/universe level sp])
(defn ty/name [name sp] [:ty/name name sp])
(defn ty/var [name sp] [:ty/var name sp])
(defn ty/app [f a sp] [:ty/app f a sp])
(defn ty/arrow [dom cod sp] [:ty/arrow dom cod sp])
(defn ty/binder [name ty sp] [:binder name ty sp])
(defn ty/pi [binder body sp] [:ty/pi binder body sp])
(defn ty/forall [binder body sp] (ty/pi binder body sp))
(defn ty/sigma [binder body sp] [:ty/sigma binder body sp])
(defn ty/exists [binder body sp] (ty/sigma binder body sp))
(defn ty/op [op args sp] [:ty/op op args sp])

(defn tm/hole [name sp] [:tm/hole name sp])
(defn tm/var [name sp] [:tm/var name sp])
(defn tm/ref [name sp] [:tm/ref name sp])
(defn tm/nat [value sp]
  (ensure-int>= value 0 "tm/nat.value >= 0")
  [:tm/nat value sp])
(defn tm/app [f a sp] [:tm/app f a sp])
(defn tm/lam [params body sp] [:tm/lam params body sp])
(defn tm/let [name value body sp] [:tm/let name value body sp])
(defn tm/op [op args sp] [:tm/op op args sp])

(defn pat/wild [sp] [:pat/wild sp])
(defn pat/hole [name sp] [:pat/hole name sp])
(defn pat/var [name sp] [:pat/var name sp])
(defn pat/con [name args sp] [:pat/con name args sp])
(defn pat/nat [value sp]
  (ensure-int>= value 0 "pat/nat.value >= 0")
  [:pat/nat value sp])

(defn decl/param [name maybe-type sp] [:param name maybe-type sp])
(defn decl/field-named [name ty sp] [:field/named name ty sp])
(defn decl/field-anon [ty sp] [:field/anon ty sp])
(defn decl/ctor-plain [name fields sp] [:ctor/plain name fields sp])
(defn decl/ctor-indexed [indices name fields sp] [:ctor/indexed indices name fields sp])
(defn decl/clause [patterns body sp] [:clause patterns body sp])

(defn decl/prec [fixity level op sp]
  (ensure |(or (= $ :infixl) (= $ :infixr) (= $ :prefix) (= $ :postfix))
          fixity
          "decl/prec.fixity")
  (ensure-int>= level 0 "decl/prec.level >= 0")
  [:decl/prec fixity level op sp])

(defn decl/data [name params ctors sp] [:decl/data name params ctors sp])
(defn decl/func [name ty clauses sp] [:decl/func name ty clauses sp])
(defn program [decls sp] [:program decls sp])

(defn node/tag [node] (if (tuple? node) (node 0) nil))

(defn- span-node? [x]
  (and (tuple? x)
       (> (length x) 0)
       (= (x 0) :span)))

(defn node/span [node]
  (if (not (tuple? node))
    nil
    (if (span-node? node)
      node
      (let [n (length node)]
        (if (> n 1)
          (let [last (node (- n 1))]
            (if (span-node? last) last nil))
          nil)))))

(defn node/type? [n]
  (let [t (node/tag n)]
    (or (= t :ty/hole) (= t :ty/universe) (= t :ty/name) (= t :ty/var)
        (= t :ty/app) (= t :ty/arrow) (= t :ty/pi) (= t :ty/sigma)
        (= t :ty/op))))

(defn node/term? [n]
  (let [t (node/tag n)]
    (or (= t :tm/hole) (= t :tm/var) (= t :tm/ref) (= t :tm/nat)
        (= t :tm/app) (= t :tm/lam) (= t :tm/let) (= t :tm/op))))

(defn node/pat? [n]
  (let [t (node/tag n)]
    (or (= t :pat/wild) (= t :pat/hole) (= t :pat/var)
        (= t :pat/con) (= t :pat/nat))))

(defn node/decl? [n]
  (let [t (node/tag n)]
    (or (= t :decl/prec) (= t :decl/data) (= t :decl/func))))

(defn- trim [s] (string/trim s))
(defn- trimr [s] (string/trimr s))
(defn- triml [s] (string/triml s))

(defn- starts-with-at? [s i pref]
  (string/has-prefix? pref (string/slice s i)))

(defn- is-byte-between? [c a b]
  (and (>= c a) (<= c b)))

(defn- is-digit-byte? [c] (is-byte-between? c (chr "0") (chr "9")))
(defn- is-upper-byte? [c] (is-byte-between? c (chr "A") (chr "Z")))
(defn- is-lower-byte? [c] (is-byte-between? c (chr "a") (chr "z")))
(defn- is-alpha-byte? [c] (or (is-upper-byte? c) (is-lower-byte? c)))
(defn- is-alnum-byte? [c] (or (is-alpha-byte? c) (is-digit-byte? c)))
(defn- is-space-byte? [c] (or (= c (chr " ")) (= c (chr "\t"))))

(defn- is-ident-start-byte? [c]
  (or (is-alpha-byte? c) (= c (chr "_"))))

(defn- is-ident-byte? [c]
  (or (is-alnum-byte? c) (= c (chr "_")) (= c (chr "-"))))

(defn- is-op-byte? [c]
  (or (= c (chr "*")) (= c (chr "+")) (= c (chr "-")) (= c (chr "/"))
      (= c (chr "<")) (= c (chr ">")) (= c (chr "=")) (= c (chr "~"))
      (= c (chr "^")) (= c (chr "@")) (= c (chr "!")) (= c (chr "?"))
      (= c (chr "|")) (= c (chr "&")) (= c (chr "%")) (= c (chr "."))))

(defn- name/is-upper? [name]
  (and (> (length name) 0)
       (is-upper-byte? (name 0))))

(defn- name/is-universe? [name]
  (and (> (length name) 1)
       (= (name 0) (chr "U"))
       (do
         (var ok true)
         (for i 1 (length name)
           (when (not (is-digit-byte? (name i)))
             (set ok false)))
         ok)))

(defn- parser/depth [p]
  (length (or (parser/state p :delimiters) "")))

(defn- parser/feed-byte! [p c text]
  (parser/byte p c)
  (when (= (parser/status p) :error)
    (errorf "parser error while scanning '%v': %v" text (parser/error p))))

(defn- split-top-level [text delim-byte]
  (let [out @[]
        p (parser/new)
        n (length text)]
    (var i 0)
    (var start 0)
    (while (< i n)
      (let [c (text i)]
        (parser/feed-byte! p c text)
        (when (and (= c delim-byte) (= (parser/depth p) 0))
          (array/push out (string/slice text start i))
          (set start (+ i 1))))
      (++ i))
    (array/push out (string/slice text start n))
    out))

(defn- split-ws-top-level [text]
  (let [out @[]
        p (parser/new)
        n (length text)]
    (var i 0)
    (var in-token false)
    (var start 0)
    (while (< i n)
      (let [c (text i)]
        (parser/feed-byte! p c text)
        (let [top? (= (parser/depth p) 0)]
          (if in-token
            (when (and top? (is-space-byte? c))
              (array/push out (string/slice text start i))
              (set in-token false))
            (when (not (is-space-byte? c))
              (set in-token true)
              (set start i)))))
      (++ i))
    (when in-token
      (array/push out (string/slice text start n)))
    out))

(defn- find-top-level-char [text target]
  (let [p (parser/new)]
    (var i 0)
    (while (< i (length text))
      (let [c (text i)]
        (parser/feed-byte! p c text)
        (when (and (= c target) (= (parser/depth p) 0))
          (return i)))
      (++ i))
    nil))

(defn syntax/default []
  @{:literals @[
      {:lit "->" :k :arrow :v :arrow}
      {:lit "=>" :k :fat-arrow :v :fat-arrow}
      {:lit "\\" :k :lambda :v :lambda}
      {:lit "λ" :k :lambda :v :lambda}
      {:lit "Π" :k :quant :v :pi}
      {:lit "∀" :k :quant :v :pi}
      {:lit "Σ" :k :quant :v :sigma}
      {:lit "∃" :k :quant :v :sigma}
    ]
    :type/quant-builders @{
      :pi ty/pi
      :sigma ty/sigma
    }
    :type/ident-resolvers @[
      (fn [name sp]
        (if (name/is-universe? name)
          (ty/universe (scan-number (string/slice name 1)) sp)
          nil))
      (fn [name sp]
        (if (name/is-upper? name)
          (ty/name name sp)
          nil))
      (fn [name sp]
        (ty/var name sp))
    ]})

(defn syntax/clone [sx]
  @{:literals (array/slice (sx :literals))
    :type/quant-builders (table/clone (sx :type/quant-builders))
    :type/ident-resolvers (array/slice (sx :type/ident-resolvers))})

(defn syntax/add-literal! [sx lit kind value]
  (array/push (sx :literals) {:lit lit :k kind :v value})
  sx)

(defn syntax/add-quant-alias! [sx alias quant-kind]
  (syntax/add-literal! sx alias :quant quant-kind)
  sx)

(defn syntax/add-type-ident-resolver! [sx resolver]
  (array/push (sx :type/ident-resolvers) resolver)
  sx)

(defn- syntax/match-literal [sx text i]
  (var best nil)
  (each entry (sx :literals)
    (let [lit (entry :lit)]
      (when (starts-with-at? text i lit)
        (if (or (nil? best)
                (> (length lit) (length (best :lit))))
          (set best entry)))))
  best)

(defn- lex [text sx]
  (let [tokens @[]
        n (length text)]
    (var i 0)
    (while (< i n)
      (let [c (text i)]
        (if (is-space-byte? c)
          (++ i)
          (if-let [lt (syntax/match-literal sx text i)]
            (do
              (array/push tokens {:k (lt :k) :v (lt :v)})
              (set i (+ i (length (lt :lit)))))
            (cond
              (= c (chr "(")) (do (array/push tokens {:k :lparen :v "("}) (++ i))
              (= c (chr ")")) (do (array/push tokens {:k :rparen :v ")"}) (++ i))
              (= c (chr ",")) (do (array/push tokens {:k :comma :v ","}) (++ i))
              (= c (chr ":")) (do (array/push tokens {:k :colon :v ":"}) (++ i))
              (= c (chr ".")) (do (array/push tokens {:k :dot :v "."}) (++ i))
              (= c (chr "=")) (do (array/push tokens {:k :eq :v "="}) (++ i))

              (= c (chr "?"))
              (let [start i]
                (++ i)
                (while (and (< i n) (is-ident-byte? (text i))) (++ i))
                (let [raw (string/slice text start i)]
                  (if (= (length raw) 1)
                    (array/push tokens {:k :hole :v nil})
                    (array/push tokens {:k :hole :v (string/slice raw 1)}))))

              (is-digit-byte? c)
              (let [start i]
                (++ i)
                (while (and (< i n) (is-digit-byte? (text i))) (++ i))
                (array/push tokens {:k :nat :v (scan-number (string/slice text start i))}))

              (is-ident-start-byte? c)
              (let [start i]
                (++ i)
                (while (and (< i n) (is-ident-byte? (text i))) (++ i))
                (let [name (string/slice text start i)]
                  (cond
                    (= name "let") (array/push tokens {:k :kw/let :v name})
                    (= name "in") (array/push tokens {:k :kw/in :v name})
                    true (array/push tokens {:k :ident :v name}))))

              (is-op-byte? c)
              (let [start i]
                (++ i)
                (while (and (< i n) (is-op-byte? (text i))) (++ i))
                (array/push tokens {:k :op :v (string/slice text start i)}))

              true
              (errorf "lex: unexpected byte %v in '%v'" c text))))))
    tokens))

(defn- pstate/new [tokens mode prec sx]
  @{:tokens tokens :i 0 :mode mode :prec prec :sx sx})

(defn- pstate/peek [st]
  (if (< (st :i) (length (st :tokens)))
    ((st :tokens) (st :i))
    {:k :eof :v nil}))

(defn- pstate/next [st]
  (let [t (pstate/peek st)]
    (put st :i (+ 1 (st :i)))
    t))

(defn- pstate/expect [st kind]
  (let [t (pstate/next st)]
    (when (not= (t :k) kind)
      (errorf "expected token %v, got %v" kind t))
    t))

(defn- prec/spec [prec op]
  (get prec op))

(defn- op-lbp [level] (+ 10 level))

(var pratt/expr nil)

(defn- parse-binder [st]
  (pstate/expect st :lparen)
  (let [nm ((pstate/expect st :ident) :v)]
    (pstate/expect st :colon)
    (let [dom (pratt/expr st 0)]
      (pstate/expect st :rparen)
      (ty/binder nm dom (span/none)))))

(defn- resolve-type-ident [st name]
  (var out nil)
  (each resolver ((st :sx) :type/ident-resolvers)
    (when (nil? out)
      (set out (resolver name (span/none)))))
  (or out (ty/var name (span/none))))

(defn- quant-builder [st q]
  (or (get ((st :sx) :type/quant-builders) q)
      (errorf "unknown quantified alias %v" q)))

(defn- nud/type [st tok]
  (match (tok :k)
    :hole (ty/hole (tok :v) (span/none))
    :ident (resolve-type-ident st (tok :v))
    :lparen (let [e (pratt/expr st 0)]
              (pstate/expect st :rparen)
              e)
    :quant
    (let [q (tok :v)
          binder (parse-binder st)]
      (pstate/expect st :dot)
      (let [body (pratt/expr st 0)
            mk (quant-builder st q)]
        (mk binder body (span/none))))
    :op
    (if-let [spec (prec/spec (st :prec) (tok :v))]
      (if (= (spec :fixity) :prefix)
        (let [rhs (pratt/expr st (op-lbp (spec :level)))]
          (ty/op (tok :v) @[rhs] (span/none)))
        (errorf "operator %v is not prefix in type position" (tok :v)))
      (errorf "unknown prefix type operator %v" (tok :v)))
    _ (errorf "unexpected type token %v" tok)))

(defn- nud/term [st tok]
  (match (tok :k)
    :hole (tm/hole (tok :v) (span/none))
    :nat (tm/nat (tok :v) (span/none))
    :ident (tm/var (tok :v) (span/none))
    :lparen (let [e (pratt/expr st 0)]
              (pstate/expect st :rparen)
              e)
    :lambda
    (let [params @[]]
      (while (= ((pstate/peek st) :k) :ident)
        (array/push params ((pstate/next st) :v)))
      (when (zero? (length params))
        (error "lambda expects at least one parameter"))
      (pstate/expect st :fat-arrow)
      (tm/lam params (pratt/expr st 0) (span/none)))
    :kw/let
    (let [name ((pstate/expect st :ident) :v)]
      (pstate/expect st :eq)
      (let [v (pratt/expr st 0)]
        (pstate/expect st :kw/in)
        (tm/let name v (pratt/expr st 0) (span/none))))
    :op
    (if-let [spec (prec/spec (st :prec) (tok :v))]
      (if (= (spec :fixity) :prefix)
        (let [rhs (pratt/expr st (op-lbp (spec :level)))]
          (tm/op (tok :v) @[rhs] (span/none)))
        (errorf "operator %v is not prefix in term position" (tok :v)))
      (errorf "unknown prefix term operator %v" (tok :v)))
    _ (errorf "unexpected term token %v" tok)))

(defn- can-start-atom? [tok]
  (let [k (tok :k)]
    (or (= k :hole) (= k :ident) (= k :nat) (= k :lparen))))

(set pratt/expr
     (fn [st min-bp]
       (let [tok (pstate/next st)
             left (if (= (st :mode) :type)
                    (nud/type st tok)
                    (nud/term st tok))]
         (var out left)
         (while true
           (let [next (pstate/peek st)
                  nk (next :k)]
             (cond
               (and (can-start-atom? next) (< min-bp 1000))
               (let [rhs (pratt/expr st 1000)]
                 (set out (if (= (st :mode) :type)
                            (ty/app out rhs (span/none))
                            (tm/app out rhs (span/none)))))

               (and (= (st :mode) :type) (= nk :arrow) (<= min-bp 20))
               (do
                 (pstate/next st)
                 (let [rhs (pratt/expr st 20)]
                    (set out (ty/arrow out rhs (span/none)))))

               (and (= nk :op)
                    (if-let [spec (prec/spec (st :prec) (next :v))]
                      (or (= (spec :fixity) :infixl)
                          (= (spec :fixity) :infixr)
                          (= (spec :fixity) :postfix))
                      false))
               (let [spec (prec/spec (st :prec) (next :v))
                     p (op-lbp (spec :level))]
                 (if (<= p min-bp)
                    (break)
                    (do
                      (pstate/next st)
                      (if (= (spec :fixity) :postfix)
                        (set out (if (= (st :mode) :type)
                                  (ty/op (next :v) @[out] (span/none))
                                  (tm/op (next :v) @[out] (span/none))))
                       (let [rbp (if (= (spec :fixity) :infixl) (+ p 1) p)
                             rhs (pratt/expr st rbp)]
                         (set out (if (= (st :mode) :type)
                                    (ty/op (next :v) @[out rhs] (span/none))
                                    (tm/op (next :v) @[out rhs] (span/none)))))))))

               true
               (break))))
         out)))

(defn- parse-with-pratt [text mode prec sx]
  (let [st (pstate/new (lex text sx) mode prec sx)
        out (pratt/expr st 0)]
    (when (not= ((pstate/peek st) :k) :eof)
      (errorf "unexpected trailing token: %v" (pstate/peek st)))
    out))

(defn parse/type-text [text &opt prec sx]
  (parse-with-pratt (trim text) :type (or prec @{}) (or sx (syntax/default))))

(defn parse/expr-text [text &opt prec sx]
  (parse-with-pratt (trim text) :term (or prec @{}) (or sx (syntax/default))))

(defn- parse/pat-atom [text]
  (let [t (trim text)
        sp (span/none)]
    (cond
      (= t "_") (pat/wild sp)
      (= t "?") (pat/hole nil sp)
      (and (> (length t) 1) (= (t 0) (chr "?"))) (pat/hole (string/slice t 1) sp)
      (and (> (length t) 0)
           (do
             (var ok true)
              (for i 0 (length t)
                (when (not (is-digit-byte? (t i)))
                  (set ok false)))
              ok)) (pat/nat (scan-number t) sp)
      true (pat/var t sp))))

(defn parse/pat-text [text]
  (let [parts (split-ws-top-level (trim text))
        sp (span/none)]
    (when (zero? (length parts))
      (error "empty pattern"))
    (if (= (length parts) 1)
      (parse/pat-atom (parts 0))
      (let [head (parse/pat-atom (parts 0))]
        (if (= (node/tag head) :pat/var)
          (let [name (head 1)
                args @[]]
            (for i 1 (length parts)
              (array/push args (parse/pat-atom (parts i))))
            (pat/con name args sp))
          head)))))

(def peg/prec-line
  (peg/compile
    ~{:ws* (any (set " \t"))
      :ws+ (some (set " \t"))
      :fix (+ (capture "infixl") (capture "infixr") (capture "prefix") (capture "postfix"))
      :lvl (capture (some (range "09")))
      :op (capture (thru -1))
      :main (* :ws* :fix :ws+ :lvl :ws+ :op :ws*)}))

(def peg/type-head-line
  (peg/compile
    ~{:ws* (any (set " \t"))
      :name (capture (* (range "AZ") (any (range "AZ" "az" "09"))))
      :params (capture (to ")"))
      :main (* :ws* :name :ws* (? (* "(" :params ")")) :ws* ":" :ws*)}))

(def peg/term-head-line
  (peg/compile
    ~{:ws* (any (set " \t"))
      :lhs (capture (some (if-not ":" 1)))
      :rhs (capture (thru -1))
      :main (* :ws* :lhs :ws* ":" :ws* :rhs)}))

(def peg/split-eq-line
  (peg/compile
    ~{:ws* (any (set " \t"))
      :lhs (capture (some (if-not "=" 1)))
      :rhs (capture (thru -1))
      :main (* :lhs :ws* "=" :ws* :rhs)}))

(defn- indent/tokenize [src]
  (let [lines (string/split "\n" src)
        out @[]]
    (for i 0 (length lines)
      (let [line (trimr (lines i))
            lnum (+ i 1)
            left (string/triml line)]
        (when (and (not= left "")
                   (not (string/has-prefix? "--" left)))
          (var col 0)
          (while (and (< col (length line)) (= (line col) (chr " "))) (++ col))
          (array/push out {:line lnum :col col :text (string/slice line col)}))))
    out))

(defn- parse/type-params [params-text prec sx]
  (if (or (nil? params-text) (= (trim params-text) ""))
    @[]
    (let [parts (split-top-level params-text (chr ","))
          out @[]]
      (each p parts
        (let [x (trim p)]
          (when (not= x "")
            (if-let [ix (find-top-level-char x (chr ":"))]
              (array/push out
                          (decl/param (trim (string/slice x 0 ix))
                                      (parse/type-text (string/slice x (+ ix 1)) prec sx)
                                      (span/none)))
              (array/push out (decl/param x nil (span/none)))))))
      out)))

(defn- parse/field-fragment [frag prec sx]
  (let [t (trim frag)
        sp (span/none)]
    (if-let [ix (find-top-level-char t (chr ":"))]
      (decl/field-named (trim (string/slice t 0 ix))
                        (parse/type-text (string/slice t (+ ix 1)) prec sx)
                        sp)
      (decl/field-anon (parse/type-text t prec sx) sp))))

(defn- read-parenthesized-end [text start]
  (let [p (parser/new)
        n (length text)]
    (var i start)
    (while (< i n)
      (parser/feed-byte! p (text i) text)
      (++ i)
      (when (= (parser/depth p) 0)
        (return i)))
    nil))

(defn- parse/fields [text prec sx]
  (let [out @[]
        n (length text)]
    (var i 0)
    (while (< i n)
      (while (and (< i n) (is-space-byte? (text i))) (++ i))
      (when (< i n)
        (if (= (text i) (chr "("))
          (if-let [end (read-parenthesized-end text i)]
            (do
              (array/push out
                          (parse/field-fragment
                            (string/slice text (+ i 1) (- end 1))
                            prec
                            sx))
              (set i end))
            (errorf "unclosed field paren: %v" text))
          (let [start i]
            (while (and (< i n) (not (is-space-byte? (text i)))) (++ i))
            (array/push out (parse/field-fragment (string/slice text start i) prec sx))))))
    out))

(defn- parse/ctor-rhs [rhs prec sx]
  (let [parts (split-ws-top-level rhs)]
    (when (zero? (length parts))
      (error "empty constructor rhs"))
    (let [name (trim (parts 0))
          rest (if (> (length parts) 1)
                 (string/slice rhs (+ (length (parts 0)) 1))
                 "")]
      [name (parse/fields rest prec sx)])))

(defn- parse/data-body-line [text prec sx]
  (if-let [eq (peg/match peg/split-eq-line text)]
    (let [lhs (trim (eq 0))
          rhs (trim (eq 1))
          idx-parts (split-top-level lhs (chr ","))
          indices @[]]
      (each p idx-parts
        (array/push indices (parse/pat-text p)))
      (let [[name fields] (parse/ctor-rhs rhs prec sx)]
        (decl/ctor-indexed indices name fields (span/none))))
    (let [[name fields] (parse/ctor-rhs (trim text) prec sx)]
      (decl/ctor-plain name fields (span/none)))))

(defn- parse/term-body-line [text prec sx]
  (if-let [eq (peg/match peg/split-eq-line text)]
      (let [lhs (trim (eq 0))
            rhs (trim (eq 1))
            pats @[]]
        (each part (split-ws-top-level lhs)
          (array/push pats (parse/pat-text part)))
      (decl/clause pats (parse/expr-text rhs prec sx) (span/none)))
    (errorf "invalid clause line: %v" text)))

(defn- classify-top [text]
  (if-let [m (peg/match peg/prec-line text)]
    [:top/prec (m 0) (scan-number (trim (m 1))) (trim (m 2))]
    (if-let [m (peg/match peg/type-head-line text)]
      [:top/type-head (m 0) (if (> (length m) 1) (m 1) nil)]
      (if-let [m (peg/match peg/term-head-line text)]
        [:top/term-head (trim (m 0)) (trim (m 1))]
        (errorf "unknown top-level line: %v" text)))))

(defn- build-prec-table [entries]
  (let [prec @{}]
    (each e entries
      (when (= (e :kind) :prec)
        (put prec (e :op) {:fixity (e :fixity) :level (e :level)})))
    prec))

(defn parse/source [src &opt sx]
  (def syntax (or sx (syntax/default)))
  (let [lines (indent/tokenize src)
        entries @[]]
    (var current nil)

    (defn flush-current []
      (when current
        (array/push entries current)
        (set current nil)))

    (each ln lines
      (if (= (ln :col) 0)
        (do
          (flush-current)
          (let [top (classify-top (ln :text))]
            (match (top 0)
              :top/prec
              (let [fx (match (top 1)
                          "infixl" :infixl
                          "infixr" :infixr
                          "prefix" :prefix
                          "postfix" :postfix
                          (errorf "unknown fixity %v" (top 1)))]
              (array/push entries {:kind :prec
                                   :fixity fx
                                   :level (top 2)
                                   :op (top 3)}))

              :top/type-head
              (set current {:kind :data-head
                            :name (top 1)
                            :params-text (top 2)
                            :body @[]})

              :top/term-head
              (set current {:kind :term-head
                            :name (top 1)
                            :type-text (top 2)
                            :body @[]}))))
        (if current
          (array/push (current :body) (ln :text))
          (errorf "indented line without declaration: %v" (ln :text)))))

    (flush-current)

    (let [prec (build-prec-table entries)
          decls @[]]
      (each e entries
        (match (e :kind)
          :prec
          (array/push decls (decl/prec (e :fixity) (e :level) (e :op) (span/none)))

          :data-head
          (let [params (parse/type-params (e :params-text) prec syntax)
                ctors @[]]
            (each bl (e :body)
              (array/push ctors (parse/data-body-line bl prec syntax)))
            (array/push decls (decl/data (e :name) params ctors (span/none))))

          :term-head
          (let [ty (parse/type-text (e :type-text) prec syntax)
                clauses @[]]
            (each bl (e :body)
              (array/push clauses (parse/term-body-line bl prec syntax)))
            (array/push decls (decl/func (e :name) ty clauses (span/none))))

          _ (errorf "unknown entry kind: %v" (e :kind))))
      (program decls (span/none)))))

(defn parse/type [x &opt prec sx]
  (if (string? x)
    (parse/type-text x (or prec @{}) (or sx (syntax/default)))
    (do
      (when (and ast/*debug-checks* (not (node/type? x)))
        (errorf "parse/type expected type node, got: %v" x))
      x)))

(defn parse/expr [x &opt prec sx]
  (if (string? x)
    (parse/expr-text x (or prec @{}) (or sx (syntax/default)))
    (do
      (when (and ast/*debug-checks* (not (node/term? x)))
        (errorf "parse/expr expected term node, got: %v" x))
      x)))

(defn parse/pat [x]
  (if (string? x)
    (parse/pat-text x)
    (do
      (when (and ast/*debug-checks* (not (node/pat? x)))
        (errorf "parse/pat expected pattern node, got: %v" x))
      x)))

(defn parse/program [x &opt sx]
  (if (string? x)
    (parse/source x (or sx (syntax/default)))
    (do
      (when (and ast/*debug-checks* (not= (node/tag x) :program))
        (errorf "parse/program expected :program node, got: %v" x))
      x)))

(def exports
  {:ast/debug-checks? ast/debug-checks?
   :ast/set-debug-checks! ast/set-debug-checks!
   :syntax/default syntax/default
   :syntax/clone syntax/clone
   :syntax/add-literal! syntax/add-literal!
   :syntax/add-quant-alias! syntax/add-quant-alias!
   :syntax/add-type-ident-resolver! syntax/add-type-ident-resolver!
   :pos pos
   :span span
   :span/none span/none

   :ty/hole ty/hole
   :ty/universe ty/universe
   :ty/name ty/name
   :ty/var ty/var
   :ty/app ty/app
   :ty/arrow ty/arrow
   :ty/binder ty/binder
   :ty/pi ty/pi
   :ty/forall ty/forall
   :ty/sigma ty/sigma
   :ty/exists ty/exists
   :ty/op ty/op

   :tm/hole tm/hole
   :tm/var tm/var
   :tm/ref tm/ref
   :tm/nat tm/nat
   :tm/app tm/app
   :tm/lam tm/lam
   :tm/let tm/let
   :tm/op tm/op

   :pat/wild pat/wild
   :pat/hole pat/hole
   :pat/var pat/var
   :pat/con pat/con
   :pat/nat pat/nat

   :decl/param decl/param
   :decl/field-named decl/field-named
   :decl/field-anon decl/field-anon
   :decl/ctor-plain decl/ctor-plain
   :decl/ctor-indexed decl/ctor-indexed
   :decl/clause decl/clause
   :decl/prec decl/prec
   :decl/data decl/data
   :decl/func decl/func
   :program program

   :node/tag node/tag
   :node/span node/span
   :node/type? node/type?
   :node/term? node/term?
   :node/pat? node/pat?
   :node/decl? node/decl?

   :parse/type parse/type
   :parse/expr parse/expr
   :parse/pat parse/pat
   :parse/type-text parse/type-text
   :parse/expr-text parse/expr-text
   :parse/pat-text parse/pat-text
   :parse/source parse/source
   :parse/program parse/program})
