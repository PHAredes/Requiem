#!/usr/bin/env janet

# Deprecated compatibility parser.
#
# Keep this module minimal: it exists only to support `src/elab_legacy.janet`
# and a small legacy test surface during the migration away from sexpr input.

(import ./deprecated :as dep)

(def grammar
  '{:ws (drop :s*)
    :stop (+ :s "(" ")" "[" "]")
    :atom (group (* (constant :atom) (<- (some (if-not :stop 1)))))
    :list (* (drop "(")
             :ws
             (group (* (constant :list) (group (any (* :node :ws)))))
             (drop ")"))
    :brackets (* (drop "[")
                 :ws
                 (group (* (constant :brackets) (group (any (* :node :ws)))))
                 (drop "]"))
    :node (+ :list :brackets :atom)
    :main (* :ws (group (any (* :node :ws))) -1)})

(def grammar/compiled
  (peg/compile grammar))

(def layout/grammar
  '{:nl (+ "\r\n" "\n" "\r")
    :hspace (set " \t")
    :line-body (any (if-not :nl 1))
    :top-line (* (if-not (+ :nl :hspace) 1) :line-body)
    :cont-line (* (some :hspace) :line-body)
    :block (<- (* :top-line (any (* :nl :cont-line)) (? :nl)))
    :comment (* (any :hspace) (+ "#" "--") :line-body (? :nl))
    :blank (* (any :hspace) :nl)
    :skip (any (+ :blank :comment))
    :main (* :skip (group (any (* :block :skip))) -1)})

(def layout/compiled
  (peg/compile layout/grammar))

(defn- node/raw->ast [raw]
  (let [tag (raw 0)
        payload (raw 1)]
    (match tag
      :atom [:atom payload]
      :list [:list (map node/raw->ast payload)]
      :brackets [:brackets (map node/raw->ast payload)]
      _ (errorf "invalid raw AST node: %v" raw))))

(defn- parse/all [p src]
  (if-let [caps (peg/match p src)]
    (if (= (length caps) 1)
      (map node/raw->ast (caps 0))
      (errorf "unexpected parser capture shape: %v" caps))
    nil))

(defn- text/starts-with? [s prefix]
  (and (>= (length s) (length prefix))
       (= (string/slice s 0 (length prefix)) prefix)))

(defn- line/indent [line]
  (defn scan [i acc]
    (if (>= i (length line))
      acc
      (let [ch (string/slice line i (+ i 1))]
        (cond
          (= ch " ") (scan (+ i 1) (+ acc 1))
          (= ch "\t") (scan (+ i 1) (+ acc 2))
          true acc))))
  (scan 0 0))

(defn- line/ignored? [line]
  (let [t (string/trim line)]
    (or (zero? (length t))
        (text/starts-with? t "#")
        (text/starts-with? t "--"))))

(defn- text/wrapped-parens? [s]
  (and (>= (length s) 2)
       (= (string/slice s 0 1) "(")
       (= (string/slice s (- (length s) 1) (length s)) ")")))

(defn- text/pipe? [s]
  (let [t (string/trim s)]
    (and (> (length t) 0)
         (= (string/slice t 0 1) "|"))))

(defn- stack/trim [stack indent]
  (if (or (<= (length stack) 1)
          (> indent (get (stack (- (length stack) 1)) :indent)))
    stack
    (stack/trim (slice stack 0 (- (length stack) 1)) indent)))

(defn- layout/pipe-split [children]
  (defn find-pipe [i]
    (if (= i (length children))
      i
      (if (text/pipe? (get (children i) :text))
        i
        (find-pipe (+ i 1)))))
  (find-pipe 0))

(defn- layout/render-node [node]
  (let [text (get node :text)
        children (get node :children)]
    (if (zero? (length children))
      text
      (let [split (layout/pipe-split children)
            head (reduce (fn [acc i]
                           (string acc " " (layout/render-node (children i))))
                         text
                         (range split))
            args (map (fn [i]
                        (let [r (layout/render-node (children i))]
                          (if (text/wrapped-parens? r)
                            r
                            (string "(" r ")"))))
                      (range split (length children)))]
        (if (zero? (length args))
          (string "(" head ")")
          (string "(" head " " (string/join args " ") ")"))))))

(defn- layout/render-top [node]
  (let [r (layout/render-node node)]
    (if (text/wrapped-parens? r)
      r
      (string "(" r ")"))))

(defn- layout/node->entry-form [node]
  [:list (reduce (fn [acc child]
                   [;acc (layout/node->entry-form child)])
                 @[[:atom "entry"]
                   [:atom (get node :text)]]
                 (get node :children))])

(defn- layout/block->record-forms [block]
  (let [root {:indent -1 :text nil :children @[]}
        lines (string/split "\n" (string block))]
    (var stack @[root])
    (each line lines
      (when (not (line/ignored? line))
        (let [indent (line/indent line)
              text (string/trim line)
              node {:indent indent :text text :children @[]}
              trimmed (stack/trim stack indent)
              parent (trimmed (- (length trimmed) 1))]
          (array/push (get parent :children) node)
          (set stack [;trimmed node]))))
    (map (fn [top]
           [:list (reduce (fn [acc child]
                            [;acc (layout/node->entry-form child)])
                          @[[:atom "record"]
                            [:atom (get top :text)]]
                          (get top :children))])
         (get root :children))))

(defn- layout/caps->forms [caps]
  (if (= (length caps) 1)
    (reduce (fn [acc block]
              (reduce (fn [inner form] [;inner form])
                      acc
                      (layout/block->record-forms block)))
            @[]
            (caps 0))
    (errorf "unexpected layout parser capture shape: %v" caps)))

(defn- block/head-line [block]
  (let [lines (string/split "\n" (string block))]
    (defn scan [rest]
      (if (zero? (length rest))
        nil
        (let [line (first rest)
              trimmed (string/trim line)]
          (if (line/ignored? line)
            (scan (slice rest 1))
            trimmed))))
    (scan lines)))

(defn- layout/legacy-block? [block]
  (if-let [head (block/head-line block)]
    (or (text/starts-with? head "data ")
        (text/starts-with? head "def ")
        (= head "data")
        (= head "def"))
    false))

(defn- layout/record-block? [block]
  (if-let [head (block/head-line block)]
    (not (nil? (string/find ":" head)))
    false))

(defn- layout/caps->mode [caps]
  (if (not= (length caps) 1)
    nil
    (let [blocks (caps 0)
          legacy? (reduce (fn [acc b] (and acc (layout/legacy-block? b))) true blocks)
          record? (reduce (fn [acc b] (and acc (layout/record-block? b))) true blocks)]
      (cond
        legacy? :legacy
        record? :record
        true nil))))

(defn- forms/all-lists? [forms]
  (reduce (fn [acc n]
            (and acc
                 (tuple? n)
                 (= (n 0) :list)))
          true
          forms))

(defn- layout/block->canonical [block]
  (let [root {:indent -1 :text nil :children @[]}
        lines (string/split "\n" (string block))]
    (var stack @[root])
    (each line lines
      (when (not (line/ignored? line))
        (let [indent (line/indent line)
              text (string/trim line)
              node {:indent indent :text text :children @[]}
              trimmed (stack/trim stack indent)
              parent (trimmed (- (length trimmed) 1))]
          (array/push (get parent :children) node)
          (set stack [;trimmed node]))))
    (let [tops (get root :children)]
      (when (zero? (length tops))
        (errorf "invalid layout block: %q" block))
      (string/join (map layout/render-top tops) "\n"))))

(defn- layout/caps->canonical [caps]
  (if (= (length caps) 1)
    (string/join (map layout/block->canonical (caps 0)) "\n")
    (errorf "unexpected layout parser capture shape: %v" caps)))

(defn layout/canonicalize [src]
  (let [txt (string src)]
    (if-let [caps (peg/match layout/compiled txt)]
      (layout/caps->canonical caps)
      (errorf "parse failed"))))

(defn parse/text [src]
  "Parse deprecated legacy source text for `src/elab_legacy.janet`."
  (dep/warn! :sexpr-parser
              "`src/frontend/sexpr/` is deprecated; prefer `src/frontend/surface/` for source parsing")
  (let [txt (string src)]
    (if-let [forms (parse/all grammar/compiled txt)]
      (if (forms/all-lists? forms)
        forms
        (if (nil? (string/find "\n" txt))
          forms
          (if-let [caps (peg/match layout/compiled txt)]
            (match (layout/caps->mode caps)
              :legacy
              (if-let [layout-forms (parse/all grammar/compiled (layout/caps->canonical caps))]
                layout-forms
                forms)
              :record
              (let [layout-forms (layout/caps->forms caps)]
                (if (zero? (length layout-forms)) forms layout-forms))
              _ forms)
            forms)))
      (if-let [caps (peg/match layout/compiled txt)]
        (match (layout/caps->mode caps)
          :legacy
          (if-let [layout-forms (parse/all grammar/compiled (layout/caps->canonical caps))]
            layout-forms
            (errorf "parse failed"))
          :record
          (let [layout-forms (layout/caps->forms caps)]
            (if (zero? (length layout-forms))
              (errorf "parse failed")
              layout-forms))
          _ (errorf "parse failed"))
        (errorf "parse failed")))))

(defn norm/layout [node]
  "Legacy helper: normalize [] and () into :list nodes."
  (match node
    [:atom _] node
    [:list xs] [:list (map norm/layout xs)]
    [:brackets xs] [:list (map norm/layout xs)]
    _ node))

(def exports
  {:parse/text parse/text
   :norm/layout norm/layout
   :layout/canonicalize layout/canonicalize})
