#!/usr/bin/env janet

(defn is-space-byte? [c]
  (or (= c (chr " ")) (= c (chr "\t"))))

# Simple paren-depth tracker for the surface language.
# Unlike Janet's parser, this only tracks () and does not
# interpret quotes, brackets, or other Janet-specific syntax.

(defn- paren-depth-byte [depth c]
  (cond
    (= c (chr "(")) (+ depth 1)
    (= c (chr ")")) (if (> depth 0) (- depth 1) 0)
    true depth))

(defn- walk-top-level [text step init]
  (let [n (length text)]
    (var i 0)
    (var depth 0)
    (var state init)
    (while (< i n)
      (let [c (text i)]
        (set depth (paren-depth-byte depth c))
        (set state (step state i c depth)))
      (++ i))
    state))

(defn split-top-level [text delim-byte]
  (let [n (length text)
        [out start]
        (walk-top-level
          text
          (fn [[out start] i c depth]
            (if (and (= c delim-byte) (= depth 0))
              (do
                (array/push out (string/slice text start i))
                [out (+ i 1)])
              [out start]))
          [@[] 0])]
    (array/push out (string/slice text start n))
    out))

(defn split-ws-top-level [text]
  (let [n (length text)
        [out in-token start]
        (walk-top-level
          text
          (fn [[out in-token start] i c depth]
            (let [top? (= depth 0)]
              (if in-token
                (if (and top? (is-space-byte? c))
                  (do
                    (array/push out (string/slice text start i))
                    [out false start])
                  [out in-token start])
                (if (is-space-byte? c)
                  [out in-token start]
                  [out true i]))))
          [@[] false 0])]
    (when in-token
      (array/push out (string/slice text start n)))
    out))

(defn find-top-level-where [text match?]
  (walk-top-level
    text
    (fn [result i c depth]
      (if (and (nil? result) (= depth 0) (match? c))
        i
        result))
    nil))

(defn find-top-level-char [text target]
  (find-top-level-where text (fn [c] (= c target))))

(defn find-first-top-level-char [text targets]
  (find-top-level-where text (fn [c] (not (nil? (find-index |(= $ c) targets))))))

(defn indent/tokenize [src]
  (let [lines (string/split "\n" src)
        out @[]]
    (eachp [i line] lines
        (let [trimmed (string/triml line)
             col (- (length line) (length trimmed))]
        (when (not= (string/trim line) "")
          (array/push out @{:text trimmed :col col :line (+ i 1)}))))
    out))

(def exports
  {:is-space-byte? is-space-byte?
   :split-top-level split-top-level
   :split-ws-top-level split-ws-top-level
   :find-top-level-char find-top-level-char
   :find-first-top-level-char find-first-top-level-char
   :indent/tokenize indent/tokenize})
