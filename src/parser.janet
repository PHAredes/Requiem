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

(defn- forms/all-lists? [forms]
  (reduce (fn [acc n]
            (and acc
                 (tuple? n)
                 (= (n 0) :list)))
          true
          forms))

(defn- layout/block->canonical [block]
  (let [raw-lines (string/split "\n" (string block))
        lines @[]]
    (each line raw-lines
      (let [t (string/trim line)]
        (when (> (length t) 0)
          (array/push lines t))))
    (when (zero? (length lines))
      (errorf "invalid layout block: %q" block))
    (let [[head args]
          (reduce (fn [state line]
                    (let [[head args] state]
                      (if (text/starts-with? line "|")
                        [head (array/push args (string "(" line ")"))]
                        [(string head " " line) args])))
                  [(lines 0) @[]]
                  (slice lines 1 (length lines)))]
      (if (zero? (length args))
        (string "(" head ")")
        (string "(" head " " (string/join args " ") ")")))))

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
