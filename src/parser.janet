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
    (errorf "parse failed")))

(defn parse/text [src]
  "Parse all top-level forms from source text (compiled PEG)."
  (parse/all grammar/compiled src))

(defn parse/text-raw [src]
  "Parse all top-level forms from source text (source PEG)."
  (parse/all grammar src))

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
   :has/atom? has/atom?})
