#!/usr/bin/env janet

# HOAS Parser - Simple recursive descent parser

(import "../src/core" :as h)

# Simple tokenizer using string split
(defn tokenize [input]
  "Split input into tokens"
  (string/split " " (string/replace-all "(" " ( " (string/replace-all ")" " ) " input))))

# Parser with index tracking
(defn parse-expr [tokens pos]
  "Parse expression starting at position pos"
  (if (>= pos (length tokens))
    (error "Unexpected end of input"))
  
  (let [token (tokens pos)]
    (match token
      ")" [(+ pos 1) nil]
      "(" (let [[new-pos expr] (parse-expr tokens (+ pos 1))
                [final-pos _] (parse-expr tokens new-pos)]
              [final-pos expr])
      "zero" [(+ pos 1) (h/tm/zero)]
      "succ" (let [[new-pos arg] (parse-expr tokens (+ pos 1))]
               [new-pos (h/tm/succ arg)])
      "app" (let [[pos1 f] (parse-expr tokens (+ pos 1))]
              (let [[pos2 x] (parse-expr tokens pos1)]
                [pos2 (h/tm/app f x)]))
      "case" (let [[pos1 s] (parse-expr tokens (+ pos 1))]
               (let [[pos2 z] (parse-expr tokens pos1)]
                 (let [[pos3 sc] (parse-expr tokens pos2)]
                   [pos3 (h/tm/case s z (fn [n] sc))])))
      "lam" (let [[pos1 var] (parse-expr tokens (+ pos 1))]
               (let [[pos2 body] (parse-expr tokens pos1)]
                 [pos2 (h/tm/lam (fn [x] body))]))
      "λ" (let [[pos1 var] (parse-expr tokens (+ pos 1))]
               (let [[pos2 body] (parse-expr tokens pos1)]
                 [pos2 (h/tm/lam (fn [x] body))]))
      "fix" (let [[new-pos f] (parse-expr tokens (+ pos 1))]
              [new-pos (h/tm/fix f)])
      "µ" (let [[new-pos f] (parse-expr tokens (+ pos 1))]
             [new-pos (h/tm/fix f)])
      "pair" (let [[pos1 l] (parse-expr tokens (+ pos 1))]
               (let [[pos2 r] (parse-expr tokens pos1)]
                 [pos2 (h/tm/pair l r)]))
      "fst" (let [[new-pos arg] (parse-expr tokens (+ pos 1))]
              [new-pos (h/tm/fst arg)])
      "snd" (let [[new-pos arg] (parse-expr tokens (+ pos 1))]
              [new-pos (h/tm/snd arg)])
      (if (>= (length token) 1) (token 0) nil)
        [(+ pos 1) (h/tm/var token)]
        (if (and (>= (length token) 1) (>= (length token) 1) (<= (token 0) "9") (>= (token 0) "0"))
          [(+ pos 1) (h/tm/var token)]
          (if (not= token "")
            [(+ pos 1) (h/tm/var token)]
            (error "string token"))))))

(defn parse [input]
  "Parse complete expression from string"
  (let [tokens (tokenize input)
        filtered (filter (fn [t] (not= t "")) tokens)]
    (let [[pos expr] (parse-expr filtered 0)]
      expr)))

# Pretty printer for terms
(defn pretty-term [term]
  "Convert term back to string representation"
  (match term
    [:var x] x
    [:zero] "zero"
    [:succ n] (string "(succ " (pretty-term n) ")")
    [:lam body] "(lam x . body)"
    [:app f x] (string "(app " (pretty-term f) " " (pretty-term x) ")")
    [:case s z sc] (string "(case " (pretty-term s) " " (pretty-term z) " " (pretty-term sc) ")")
    [:fix f] (string "(fix " (pretty-term f) ")")
    [:pair l r] (string "(pair " (pretty-term l) " " (pretty-term r) ")")
    [:fst p] (string "(fst " (pretty-term p) ")")
    [:snd p] (string "(snd " (pretty-term p) ")")
    [:nnat n] (string n)
    [:nneut ne] (string "neutral:" (pretty-term ne))
    [:nvar x] (string "nvar:" x)
    [:napp f x] (string "(" (pretty-term f) " " (pretty-term x) ")")
    _ (string term)))

# Export functions
(def exports {
  :parse parse
  :tokenize tokenize
  :pretty-term pretty-term
})