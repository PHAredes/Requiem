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

(defn decl/data [name params sort ctors sp] [:decl/data name params sort ctors sp])
(defn decl/func [name ty clauses sp] [:decl/func name ty clauses sp])
(defn decl/compute [tm sp] [:decl/compute tm sp])
(defn decl/check [tm ty sp] [:decl/check tm ty sp])
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

(defn node/type-or-term? [n]
  (or (node/type? n) (node/term? n)))

(defn node/pat? [n]
  (let [t (node/tag n)]
    (or (= t :pat/wild) (= t :pat/hole) (= t :pat/var)
        (= t :pat/con) (= t :pat/nat))))

(defn node/decl? [n]
  (let [t (node/tag n)]
    (or (= t :decl/prec) (= t :decl/data) (= t :decl/func)
        (= t :decl/compute) (= t :decl/check))))

(def exports
  {:ast/debug-checks? ast/debug-checks?
   :ast/set-debug-checks! ast/set-debug-checks!
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
   :decl/compute decl/compute
   :decl/check decl/check
   :program program
   :node/tag node/tag
   :node/span node/span
   :node/type? node/type?
   :node/term? node/term?
   :node/pat? node/pat?
   :node/decl? node/decl?})
