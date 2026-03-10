#!/usr/bin/env janet

(defn trim [s] (string/trim s))
(defn trimr [s] (string/trimr s))
(defn triml [s] (string/triml s))

(defn is-space-byte? [c]
  (or (= c (chr " ")) (= c (chr "\t"))))

(defn- parser/depth [p]
  (length (or (parser/state p :delimiters) "")))

(defn- parser/feed-byte! [p c text]
  (parser/byte p c)
  (when (= (parser/status p) :error)
    (errorf "parser error while scanning '%v': %v" text (parser/error p))))

(defn split-top-level [text delim-byte]
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

(defn split-ws-top-level [text]
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

(defn find-top-level-char [text target]
  (let [p (parser/new)]
    (var i 0)
    (while (< i (length text))
      (let [c (text i)]
        (parser/feed-byte! p c text)
        (when (and (= c target) (= (parser/depth p) 0))
          (return i)))
      (++ i))
    nil))

(def exports
  {:trim trim
   :trimr trimr
   :triml triml
   :is-space-byte? is-space-byte?
   :split-top-level split-top-level
   :split-ws-top-level split-ws-top-level
   :find-top-level-char find-top-level-char})
