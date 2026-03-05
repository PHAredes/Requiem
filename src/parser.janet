#!/usr/bin/env janet

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
    :top-head (+ "data" "def")
    :top-line (* :top-head :line-body)
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
  (reduce (fn [acc i]
            (let [ch (string/slice line i (+ i 1))]
              (cond
                (= ch " ") (+ acc 1)
                (= ch "\t") (+ acc 2)
                true acc)))
          0
          (range 0 (length line))))

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
    (defn walk [rest stack]
      (if (zero? (length rest))
        nil
        (let [line (first rest)]
          (if (line/ignored? line)
            (walk (slice rest 1) stack)
            (let [indent (line/indent line)
                  text (string/trim line)
                  node {:indent indent :text text :children @[]}
                  trimmed (stack/trim stack indent)
                  parent (trimmed (- (length trimmed) 1))]
              (array/push (get parent :children) node)
              (walk (slice rest 1) [;trimmed node]))))))
    (walk lines @[root])
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
  "Parse all top-level forms from source text, using PEG layout fallback."
  (let [txt (string src)]
    (if-let [forms (parse/all grammar/compiled txt)]
      (if (forms/all-lists? forms)
        forms
        (if (nil? (string/find "\n" txt))
          forms
          (if-let [caps (peg/match layout/compiled txt)]
            (if-let [layout-forms (parse/all grammar/compiled (layout/caps->canonical caps))]
              layout-forms
              forms)
            forms)))
      (if-let [caps (peg/match layout/compiled txt)]
        (if-let [layout-forms (parse/all grammar/compiled (layout/caps->canonical caps))]
          layout-forms
          (errorf "parse failed"))
        (errorf "parse failed")))))

(defn parse/text-raw [src]
  "Parse all top-level forms from source text (source PEG)."
  (if-let [forms (parse/all grammar (string src))]
    forms
    (errorf "parse failed")))

(defn parse/one [src]
  "Parse exactly one top-level form from source text."
  (let [forms (parse/text src)]
    (if (= (length forms) 1)
      (forms 0)
      (errorf "expected one top-level form, got %d" (length forms)))))

(defn render/node [node]
  (match node
    [:atom tok] tok
    [:list xs] (string "(" (string/join (map render/node xs) " ") ")")
    [:brackets xs] (string "[" (string/join (map render/node xs) " ") "]")
    _ (errorf "render/node: invalid raw node %v" node)))

(defn render/program [forms]
  "Render parsed forms into canonical text."
  (string/join (map render/node forms) "\n"))

(defn norm/layout [node]
  "Layout-only normalization: [] and () become :list."
  (match node
    [:atom _] node
    [:list xs] [:list (map norm/layout xs)]
    [:brackets xs] [:list (map norm/layout xs)]
    _ node))

(defn norm/program [forms]
  "Apply layout normalization over a full program."
  (map norm/layout forms))

(defn has/atom? [node tok]
  "Check if token appears anywhere in a raw node."
  (match node
    [:atom x] (= x tok)
    [:list xs] (reduce (fn [acc n] (or acc (has/atom? n tok))) false xs)
    [:brackets xs] (reduce (fn [acc n] (or acc (has/atom? n tok))) false xs)
    _ false))

(def exports
  {:grammar grammar
   :grammar/compiled grammar/compiled
   :parse/text parse/text
   :parse/text-raw parse/text-raw
   :parse/one parse/one
   :render/node render/node
   :render/program render/program
   :norm/layout norm/layout
   :norm/program norm/program
   :layout/canonicalize layout/canonicalize
   :has/atom? has/atom?})
