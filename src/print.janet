#!/usr/bin/env janet

(defn make [deps]
  (let [T/Type (deps :T/Type)
        T/Pi (deps :T/Pi)
        T/Sigma (deps :T/Sigma)
        T/Id (deps :T/Id)
        T/Refl (deps :T/Refl)
        T/Neutral (deps :T/Neutral)
        T/Meta (deps :T/Meta)
        T/Pair (deps :T/Pair)
        NF/Neut (deps :NF/Neut)
        NF/Lam (deps :NF/Lam)
        NF/Pi (deps :NF/Pi)
        NF/Sigma (deps :NF/Sigma)
        NF/Type (deps :NF/Type)
        NF/Pair (deps :NF/Pair)
        NF/Id (deps :NF/Id)
        NF/Refl (deps :NF/Refl)
        ty/type (deps :ty/type)
        lower (deps :lower)
        lvl/str (deps :lvl/str)]
    (var state/name-map nil)
    (var state/used-names nil)
    (var state/fresh-id 0)
    (var print/ne* nil)
    (var print/nf* nil)
    (var print/tm* nil)

    (defn state/reset! []
      (set state/fresh-id 0)
      (set state/name-map @{})
      (set state/used-names @{}))

    (defn state/mark-used! [name]
      (put state/used-names name true)
      name)

    (defn state/used? [name]
      (get state/used-names name))

    (defn internal-name? [x]
      (let [s (string x)]
        (and (> (length s) 0)
             (= (s 0) (chr "_")))))

    (def letters "abcdefghijklmnopqrstuvwxyz")

    (defn alpha-name [n]
      (let [q (div n (length letters))
            r (% n (length letters))
            ch (string/slice letters r (+ r 1))]
        (if (= q 0)
          ch
          (string (alpha-name (- q 1)) ch))))

    (defn find-name [n build]
      (var i n)
      (while (state/used? (build i)) (++ i))
      [i (build i)])

    (defn fresh-name []
      (let [[n candidate] (find-name state/fresh-id alpha-name)]
        (set state/fresh-id (inc n))
        (state/mark-used! candidate)))

    (defn disambiguate [preferred]
      (if (not (state/used? preferred))
        (state/mark-used! preferred)
        (let [[_ candidate] (find-name 1 (fn [n] (string preferred n)))]
          (state/mark-used! candidate))))

    (defn name [x]
      (or (get state/name-map x)
          (let [preferred (string x)
                out (if (internal-name? x)
                      (fresh-name)
                      (disambiguate preferred))]
            (put state/name-map x out)
            out)))

    (defn wrap [s]
      (string "(" s ")"))

    (defn tag-of [x]
      (if (tuple? x) (get x 0) 0))

    (defn atomic-ne? [ne]
      (match ne
        [:nvar _] true
        [:nmeta _] true
        _ false))

    (defn atomic-nf? [nf]
      (match nf
        [NF/Type _] true
        [NF/Neut [:nvar _]] true
        _ false))

    (defn atomic-tm? [tm]
      (match tm
        [:var _] true
        [:type _] true
        [:hole _] true
        _ false))

    (defn ne-arg [ne]
      (let [rendered (print/ne* ne)]
        (if (atomic-ne? ne) rendered (wrap rendered))))

    (defn nf-arg [nf]
      (let [rendered (print/nf* nf)]
        (if (atomic-nf? nf) rendered (wrap rendered))))

    (defn tm-arg [tm]
      (let [rendered (print/tm* tm)]
        (if (atomic-tm? tm) rendered (wrap rendered))))

    (defn render-nf-binder [label A B]
      (let [x (fresh-name)]
        (string label "(" x " : " (print/nf* A) "). " (print/nf* (B x)))))

    (defn render-tm-binder [label A B]
      (let [x (fresh-name)]
        (string label "(" x " : " (print/tm* A) "). " (print/tm* (B [:var x])))))

    (set print/ne*
         (fn [ne]
           (match ne
             [:nvar x] (name x)
             [:nmeta id] (string "?" id)
             [:napp f x] (string (ne-arg f) " " (nf-arg x))
             [:nfst p] (string "fst " (ne-arg p))
             [:nsnd p] (string "snd " (ne-arg p))
             [:nJ A x P d y p]
             (string "J "
                     (nf-arg A) " "
                     (nf-arg x) " "
                     (nf-arg P) " "
                     (nf-arg d) " "
                     (nf-arg y) " "
                     (ne-arg p))
             _ (string/format "%v" ne))))

    (set print/nf*
         (fn [nf]
            (match nf
              [NF/Type l]
              (string "Type" (lvl/str l))

              [NF/Pi A B]
              (render-nf-binder "Pi" A B)

              [NF/Sigma A B]
              (render-nf-binder "Sigma" A B)

             [NF/Id A x y]
             (string "Id " (nf-arg A) " " (nf-arg x) " " (nf-arg y))

             [NF/Refl x]
             (string "refl " (nf-arg x))

             [NF/Pair l r]
             (string "(" (print/nf* l) ", " (print/nf* r) ")")

              [NF/Lam body]
              (let [x (fresh-name)]
                (string "λ" x "." (print/nf* (body x))))

             [NF/Neut ne]
             (print/ne* ne)

             _
             (string/format "%v" nf))))

    (set print/tm*
         (fn [tm]
           (match tm
             [:var x]
             (name x)

             [:app f x]
             (string (tm-arg f) " " (tm-arg x))

              [:type l]
              (string "Type" (lvl/str l))

              [:lam body]
              (let [x (fresh-name)]
                (string "λ" x "." (print/tm* (body [:var x]))))

              [:t-pi A B]
              (render-tm-binder "Pi" A B)

              [:t-sigma A B]
              (render-tm-binder "Sigma" A B)

             [:pair l r]
             (string "(" (print/tm* l) ", " (print/tm* r) ")")

             [:fst p]
             (string "fst " (tm-arg p))

             [:snd p]
             (string "snd " (tm-arg p))

             [:t-id A x y]
             (string "Id " (tm-arg A) " " (tm-arg x) " " (tm-arg y))

             [:t-refl x]
             (string "refl " (tm-arg x))

             [:t-J A x P d y p]
             (string "J "
                     (tm-arg A) " "
                     (tm-arg x) " "
                     (tm-arg P) " "
                     (tm-arg d) " "
                     (tm-arg y) " "
                     (tm-arg p))

             [:hole name]
             (if name (string "?" name) "?")

             _
             (string/format "%v" tm))))

    (defn state/snapshot []
      [state/fresh-id state/name-map state/used-names])

    (defn state/restore! [snapshot]
      (let [[saved-id saved-map saved-used] snapshot]
        (set state/fresh-id saved-id)
        (set state/name-map saved-map)
        (set state/used-names saved-used)))

    (defn with-state [f]
      (let [snapshot (state/snapshot)]
        (state/reset!)
        (try
          (let [out (f)]
            (state/restore! snapshot)
            out)
          ([err]
           (state/restore! snapshot)
           (error err)))))

    (defn print/ne [ne]
      (with-state (fn [] (print/ne* ne))))

    (defn print/nf [nf]
      (with-state (fn [] (print/nf* nf))))

    (defn print/tm [tm]
      (with-state (fn [] (print/tm* tm))))

    (defn sem* [sem]
      (let [tag (tag-of sem)]
        (cond
          (= tag T/Neutral) (print/ne* (get sem 1))
          (= tag T/Meta) (string "?" (get sem 1))
          (= tag T/Refl) (string "refl " (sem* (get sem 1)))
          (= tag T/Pair) (string "(" (sem* (get sem 1)) ", " (sem* (get sem 2)) ")")
          (or (= tag T/Type) (= tag T/Pi) (= tag T/Sigma) (= tag T/Id))
          (print/nf* (lower (ty/type 100) sem))
          true (string/format "%v" sem))))

    (defn print/sem [sem]
      (with-state (fn [] (sem* sem))))

    {:print/tm print/tm
     :print/nf print/nf
     :print/ne print/ne
     :print/sem print/sem}))

(def exports {:make make})
