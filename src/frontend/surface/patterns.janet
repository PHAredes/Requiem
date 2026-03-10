#!/usr/bin/env janet

(import ./ast :as a)
(import ./layout :as ly)
(import ./lexer :as lx)

(defn- parse/pat-atom [text]
  (let [t (ly/trim text)
        sp (a/span/none)]
    (cond
      (= t "_") (a/pat/wild sp)
      (= t "?") (a/pat/hole nil sp)
      (and (> (length t) 1) (= (t 0) (chr "?"))) (a/pat/hole (string/slice t 1) sp)
      (and (> (length t) 0)
           (do
             (var ok true)
             (for i 0 (length t)
               (when (not (lx/is-digit-byte? (t i)))
                 (set ok false)))
             ok)) (a/pat/nat (scan-number t) sp)
      true (a/pat/var t sp))))

(defn parse/pat-text [text]
  (let [parts (ly/split-ws-top-level (ly/trim text))
        sp (a/span/none)]
    (when (zero? (length parts))
      (error "empty pattern"))
    (if (= (length parts) 1)
      (parse/pat-atom (parts 0))
      (let [head (parse/pat-atom (parts 0))]
        (if (= (a/node/tag head) :pat/var)
          (let [name (head 1)
                args @[]]
            (for i 1 (length parts)
              (array/push args (parse/pat-atom (parts i))))
            (a/pat/con name args sp))
          head)))))

(def exports
  {:parse/pat-text parse/pat-text})
