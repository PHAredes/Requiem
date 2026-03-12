#!/usr/bin/env janet

(import ./syntax :as x)

(defn- is-byte-between? [c a b]
  (and (>= c a) (<= c b)))

(defn is-digit-byte? [c] (is-byte-between? c (chr "0") (chr "9")))
(defn- is-upper-byte? [c] (is-byte-between? c (chr "A") (chr "Z")))
(defn- is-lower-byte? [c] (is-byte-between? c (chr "a") (chr "z")))
(defn- is-alpha-byte? [c] (or (is-upper-byte? c) (is-lower-byte? c)))
(defn- is-alnum-byte? [c] (or (is-alpha-byte? c) (is-digit-byte? c)))
(defn is-space-byte? [c] (or (= c (chr " ")) (= c (chr "\t"))))

(defn- is-ident-start-byte? [c]
  (or (is-alpha-byte? c) (= c (chr "_"))))

(defn- is-ident-byte? [c]
  (or (is-alnum-byte? c) (= c (chr "_")) (= c (chr "-")) (= c (chr "'"))))

(defn is-op-byte? [c]
  (or (= c (chr "*")) (= c (chr "+")) (= c (chr "-")) (= c (chr "/"))
      (= c (chr "<")) (= c (chr ">")) (= c (chr "=")) (= c (chr "~"))
      (= c (chr "^")) (= c (chr "@")) (= c (chr "!")) (= c (chr "?"))
      (= c (chr "|")) (= c (chr "&")) (= c (chr "%")) (= c (chr "."))))

(defn- token/new [k v line col]
  {:k k :v v :line line :col col})

(defn- scan-while [text start pred]
  (let [n (length text)]
    (var i start)
    (while (and (< i n) (pred (text i)))
      (++ i))
    i))

(defn lex [text sx]
  (let [tokens @[]
         n (length text)]
    (var i 0)
    (var line 1)
    (var col 1)
    (while (< i n)
      (let [c (text i)]
        (if (or (is-space-byte? c) (= c (chr "\n")))
          (do
            (++ i)
            (if (= c (chr "\n"))
              (do (++ line) (set col 1))
              (++ col)))
          (if-let [lt (x/syntax/match-literal sx text i)]
            (do
              (array/push tokens (token/new (lt :k) (lt :v) line col))
              (let [lit-len (length (lt :lit))]
                (set i (+ i lit-len))
                (set col (+ col lit-len))))
            (cond
              (= c (chr "(")) (do (array/push tokens (token/new :lparen "(" line col)) (++ i) (++ col))
              (= c (chr ")")) (do (array/push tokens (token/new :rparen ")" line col)) (++ i) (++ col))
              (= c (chr ",")) (do (array/push tokens (token/new :comma "," line col)) (++ i) (++ col))
              (= c (chr ":")) (do (array/push tokens (token/new :colon ":" line col)) (++ i) (++ col))
              (= c (chr ".")) (do (array/push tokens (token/new :dot "." line col)) (++ i) (++ col))
              (= c (chr "=")) (do (array/push tokens (token/new :eq "=" line col)) (++ i) (++ col))

              (= c (chr "?"))
              (let [start i
                     start-col col]
                 (++ i)
                 (++ col)
                 (set i (scan-while text i is-ident-byte?))
                 (set col (+ start-col (- i start)))
                 (let [raw (string/slice text start i)]
                   (if (= (length raw) 1)
                     (array/push tokens (token/new :hole nil line start-col))
                     (array/push tokens (token/new :hole (string/slice raw 1) line start-col)))))

              (is-digit-byte? c)
              (let [start i
                     start-col col]
                 (++ i)
                 (++ col)
                 (set i (scan-while text i is-digit-byte?))
                 (set col (+ start-col (- i start)))
                 (array/push tokens (token/new :nat (scan-number (string/slice text start i)) line start-col)))

              (is-ident-start-byte? c)
              (let [start i
                     start-col col]
                 (++ i)
                 (++ col)
                 (set i (scan-while text i is-ident-byte?))
                 (set col (+ start-col (- i start)))
                 (let [name (string/slice text start i)]
                   (cond
                    (= name "let") (array/push tokens (token/new :kw/let name line start-col))
                    (= name "in") (array/push tokens (token/new :kw/in name line start-col))
                    true (array/push tokens (token/new :ident name line start-col)))))

              (is-op-byte? c)
              (let [start i
                     start-col col]
                 (++ i)
                 (++ col)
                 (set i (scan-while text i is-op-byte?))
                 (set col (+ start-col (- i start)))
                 (array/push tokens (token/new :op (string/slice text start i) line start-col)))

              true
              (errorf "lex error at %d:%d: unexpected byte %q" line col c))))))
    tokens))

(def exports
  {:is-digit-byte? is-digit-byte?
   :is-space-byte? is-space-byte?
   :is-op-byte? is-op-byte?
   :lex lex})
