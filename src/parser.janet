#!/usr/bin/env janet

# Lispy parser for the surface language (no precedence / associativity)

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

(defn- node/raw->ast [raw]
  (let [tag (raw 0)
        payload (raw 1)]
    (match tag
      :atom [:atom payload]
      :list [:list (map node/raw->ast payload)]
      :brackets [:brackets (map node/raw->ast payload)]
      _ (errorf "invalid raw AST node: %v\nExpected nodes are tagged :atom, :list, or :brackets\nCheck the parser grammar for valid node types" raw))))

(defn- parse/all [p src]
  (if-let [caps (peg/match p src)]
    (if (= (length caps) 1)
      (map node/raw->ast (caps 0))
      (errorf "unexpected parser capture shape: %v" caps))
    nil))

(defn- line/indent [line]
  (var i 0)
  (var acc 0)
  (while (< i (length line))
    (let [ch (string/slice line i (+ i 1))]
      (if (= ch " ")
        (do (++ i) (++ acc))
        (if (= ch "\t")
          (do (++ i) (set acc (+ acc 2)))
          (break)))))
  acc)

(defn- line/ignored? [line]
  (let [t (string/trim line)]
    (or (zero? (length t))
        (and (> (length t) 0) (= (string/slice t 0 1) "#"))
        (and (>= (length t) 2)
             (= (string/slice t 0 2) "--")))))

(defn- stack/top [stack]
  (stack (- (length stack) 1)))

(defn- text/starts-with? [s prefix]
  (and (>= (length s) (length prefix))
       (= (string/slice s 0 (length prefix)) prefix)))

(defn- text/wrapped-parens? [s]
  (and (>= (length s) 2)
       (= (string/slice s 0 1) "(")
       (= (string/slice s (- (length s) 1) (length s)) ")")))

(defn- text/pipe? [s]
  (let [t (string/trim s)]
    (and (> (length t) 0)
         (= (string/slice t 0 1) "|"))))

(var layout/render-node nil)

(defn- layout/render-arg [node]
  (let [r (layout/render-node node)]
    (if (text/wrapped-parens? r)
      r
      (string "(" r ")"))))

(defn- layout/render-top [node]
  (let [r (layout/render-node node)]
    (if (text/wrapped-parens? r)
      r
      (string "(" r ")"))))

(set layout/render-node
     (fn [node]
       (let [text (get node :text)
             children (get node :children)]
         (if (zero? (length children))
           text
           (let [head text
                 n (length children)]
             (var head head)
             (var split n)
             (for i 0 n
               (when (and (= split n) (text/pipe? (get (children i) :text)))
                 (set split i)))
             (for i 0 split
               (set head (string head " " (layout/render-node (children i)))))
             (let [args @[]]
               (for i split n
                 (array/push args (layout/render-arg (children i))))
               (if (zero? (length args))
                 (string "(" head ")")
                 (string "(" head " " (string/join args " ") ")"))))))))

(defn layout/desweet [src]
  (let [txt (string src)
        root {:indent -1 :text nil :children @[]}
        stack @[root]]
    (each line (string/split "\n" txt)
      (when (not (line/ignored? line))
        (let [indent (line/indent line)
              text (string/trim line)
              node {:indent indent :text text :children @[]}]
          (while (and (> (length stack) 1)
                      (<= indent (get (stack/top stack) :indent)))
            (array/pop stack))
          (array/push (get (stack/top stack) :children) node)
          (array/push stack node))))
    (string/join (map layout/render-top (get root :children)) "\n")))

(defn- forms/all-lists? [forms]
  (reduce (fn [acc n]
            (and acc
                 (tuple? n)
                 (= (n 0) :list)))
          true
          forms))

(defn parse/text [src]
  "Parse all top-level forms from source text (compiled PEG), with sweet-layout fallback."
  (let [txt (string src)
        sweet? (not (nil? (string/find "\n" txt)))]
    (if-let [forms (parse/all grammar/compiled txt)]
      (if (or (forms/all-lists? forms) (not sweet?))
        forms
        (let [rewritten (layout/desweet txt)]
          (if-let [fallback (parse/all grammar/compiled rewritten)]
            (if (forms/all-lists? fallback)
              fallback
              forms)
            forms)))
      (if sweet?
        (let [rewritten (layout/desweet txt)]
          (if-let [fallback (parse/all grammar/compiled rewritten)]
            fallback
            (errorf "parse failed")))
        (errorf "parse failed")))))

(defn parse/text-raw [src]
  "Parse all top-level forms from source text (source PEG)."
  (if-let [forms (parse/all grammar src)]
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
   :layout/desweet layout/desweet
   :has/atom? has/atom?})
