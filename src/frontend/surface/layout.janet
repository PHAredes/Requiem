#!/usr/bin/env janet

(defn trim [s] (string/trim s))
(defn trimr [s] (string/trimr s))
(defn triml [s] (string/triml s))

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

(defn split-top-level [text delim-byte]
  (let [out @[]
        n (length text)]
    (var i 0)
    (var start 0)
    (var depth 0)
    (while (< i n)
      (let [c (text i)]
        (set depth (paren-depth-byte depth c))
        (when (and (= c delim-byte) (= depth 0))
          (array/push out (string/slice text start i))
          (set start (+ i 1))))
      (++ i))
    (array/push out (string/slice text start n))
    out))

(defn split-ws-top-level [text]
  (let [out @[]
        n (length text)]
    (var i 0)
    (var in-token false)
    (var start 0)
    (var depth 0)
    (while (< i n)
      (let [c (text i)]
        (set depth (paren-depth-byte depth c))
        (let [top? (= depth 0)]
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

(defn find-top-level-char [text target]
  (var i 0)
  (var depth 0)
  (var found false)
  (var result nil)
  (while (and (< i (length text)) (not found))
    (let [c (text i)]
      (set depth (paren-depth-byte depth c))
      (when (and (= c target) (= depth 0))
        (set found true)
        (set result i)))
    (++ i))
  result)

(def exports
  {:trim trim
   :trimr trimr
   :triml triml
   :is-space-byte? is-space-byte?
   :split-top-level split-top-level
   :split-ws-top-level split-ws-top-level
   :find-top-level-char find-top-level-char})
