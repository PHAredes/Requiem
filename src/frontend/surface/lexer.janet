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

(defn lex [text sx]
  (let [tokens @[]
        n (length text)]
    (var i 0)
    (while (< i n)
      (let [c (text i)]
        (if (is-space-byte? c)
          (++ i)
          (if-let [lt (x/syntax/match-literal sx text i)]
            (do
              (array/push tokens {:k (lt :k) :v (lt :v)})
              (set i (+ i (length (lt :lit)))))
            (cond
              (= c (chr "(")) (do (array/push tokens {:k :lparen :v "("}) (++ i))
              (= c (chr ")")) (do (array/push tokens {:k :rparen :v ")"}) (++ i))
              (= c (chr ",")) (do (array/push tokens {:k :comma :v ","}) (++ i))
              (= c (chr ":")) (do (array/push tokens {:k :colon :v ":"}) (++ i))
              (= c (chr ".")) (do (array/push tokens {:k :dot :v "."}) (++ i))
              (= c (chr "=")) (do (array/push tokens {:k :eq :v "="}) (++ i))

              (= c (chr "?"))
              (let [start i]
                (++ i)
                (while (and (< i n) (is-ident-byte? (text i))) (++ i))
                (let [raw (string/slice text start i)]
                  (if (= (length raw) 1)
                    (array/push tokens {:k :hole :v nil})
                    (array/push tokens {:k :hole :v (string/slice raw 1)}))))

              (is-digit-byte? c)
              (let [start i]
                (++ i)
                (while (and (< i n) (is-digit-byte? (text i))) (++ i))
                (array/push tokens {:k :nat :v (scan-number (string/slice text start i))}))

              (is-ident-start-byte? c)
              (let [start i]
                (++ i)
                (while (and (< i n) (is-ident-byte? (text i))) (++ i))
                (let [name (string/slice text start i)]
                  (cond
                    (= name "let") (array/push tokens {:k :kw/let :v name})
                    (= name "in") (array/push tokens {:k :kw/in :v name})
                    true (array/push tokens {:k :ident :v name}))))

              (is-op-byte? c)
              (let [start i]
                (++ i)
                (while (and (< i n) (is-op-byte? (text i))) (++ i))
                (array/push tokens {:k :op :v (string/slice text start i)}))

              true
              (errorf "lex: unexpected byte %v in '%v'" c text))))))
    tokens))

(def exports
  {:is-digit-byte? is-digit-byte?
   :is-space-byte? is-space-byte?
   :is-op-byte? is-op-byte?
   :lex lex})
