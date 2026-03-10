#!/usr/bin/env janet

(import ./coreTT :as tt)
(import ./levels :as lvl)

(var state/name-map nil)
(var state/used-names nil)
(var state/fresh-id 0)

(defn- state/reset! []
  (set state/fresh-id 0)
  (set state/name-map @{})
  (set state/used-names @{}))

(defn- state/mark-used! [name]
  (put state/used-names name true)
  name)

(defn- state/used? [name]
  (get state/used-names name))

(defn- internal-name? [x]
  (let [s (string x)]
    (and (> (length s) 0)
         (= (s 0) (chr "_")))))

(defn- alpha-name [n]
  (let [letters "abcdefghijklmnopqrstuvwxyz"]
    (defn recur [k]
      (let [q (div k 26)
            r (% k 26)
            ch (string/slice letters r (+ r 1))]
        (if (= q 0)
          ch
          (string (recur (- q 1)) ch))))
    (recur n)))

(defn- fresh-name []
  (var out nil)
  (while (nil? out)
    (let [candidate (alpha-name state/fresh-id)]
      (++ state/fresh-id)
      (when (not (state/used? candidate))
        (set out (state/mark-used! candidate)))))
  out)

(defn- disambiguate [preferred]
  (if (not (state/used? preferred))
    (state/mark-used! preferred)
    (do
      (var out nil)
      (var n 1)
      (while (nil? out)
        (let [candidate (string preferred n)]
          (if (state/used? candidate)
            (++ n)
            (set out (state/mark-used! candidate)))))
      out)))

(defn- name [x]
  (or (get state/name-map x)
      (let [preferred (string x)
            out (if (internal-name? x)
                  (fresh-name)
                  (disambiguate preferred))]
        (put state/name-map x out)
        out)))

(defn- wrap [s]
  (string "(" s ")"))

(var print/ne* nil)
(var print/nf* nil)
(var print/tm* nil)

(defn- atomic-ne? [ne]
  (match ne
    [:nvar _] true
    _ false))

(defn- atomic-nf? [nf]
  (let [tag (if (tuple? nf) (get nf 0) nil)]
    (or (and (= tag tt/NF/Type))
        (and (= tag tt/NF/Neut)
             (tuple? (get nf 1))
             (= ((get nf 1) 0) :nvar)))))

(defn- atomic-tm? [tm]
  (match tm
    [:var _] true
    [:type _] true
    [:hole _] true
    _ false))

(defn- level-text [l]
  (cond
    (int? l) (string (lvl/value l))
    (lvl/const? l) (string (lvl/value l))
    (lvl/shift? l) (string (lvl/value l))
    (and (tuple? l) (> (length l) 1) (int? (get l 1))) (string (get l 1))
    true (string/format "%v" l)))

(defn- ne-arg [ne]
  (let [rendered (print/ne* ne)]
    (if (atomic-ne? ne) rendered (wrap rendered))))

(defn- nf-arg [nf]
  (let [rendered (print/nf* nf)]
    (if (atomic-nf? nf) rendered (wrap rendered))))

(defn- tm-arg [tm]
  (let [rendered (print/tm* tm)]
    (if (atomic-tm? tm) rendered (wrap rendered))))

(set print/ne*
     (fn [ne]
       (match ne
         [:nvar x] (name x)
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
       (let [tag (if (tuple? nf) (get nf 0) nil)]
         (cond
           (= tag tt/NF/Type)
           (let [l (get nf 1)]
             (string "Type" (level-text l)))

           (= tag tt/NF/Pi)
           (let [A (get nf 1)
                 B (get nf 2)
                 x (fresh-name)]
             (string "Pi(" x " : " (print/nf* A) "). " (print/nf* (B x))))

           (= tag tt/NF/Sigma)
           (let [A (get nf 1)
                 B (get nf 2)
                 x (fresh-name)]
             (string "Sigma(" x " : " (print/nf* A) "). " (print/nf* (B x))))

           (= tag tt/NF/Id)
           (string "Id " (nf-arg (get nf 1)) " " (nf-arg (get nf 2)) " " (nf-arg (get nf 3)))

           (= tag tt/NF/Refl)
           (string "refl " (nf-arg (get nf 1)))

           (= tag tt/NF/Pair)
           (string "(" (print/nf* (get nf 1)) ", " (print/nf* (get nf 2)) ")")

           (= tag tt/NF/Lam)
           (let [body (get nf 1)
                 x (fresh-name)]
             (string "λ" x ". " (print/nf* (body x))))

           (= tag tt/NF/Neut)
           (print/ne* (get nf 1))

            true (string/format "%v" nf)))))

(set print/tm*
     (fn [tm]
       (match tm
         [:var x] (name x)
         [:app f x] (string (tm-arg f) " " (tm-arg x))
         [:type l] (string "Type" l)
         [:lam body]
         (let [x (fresh-name)]
           (string "λ" x ". " (print/tm* (body [:var x]))))
         [:t-pi A B]
         (let [x (fresh-name)]
           (string "Pi(" x " : " (print/tm* A) "). " (print/tm* (B [:var x]))))
         [:t-sigma A B]
         (let [x (fresh-name)]
           (string "Sigma(" x " : " (print/tm* A) "). " (print/tm* (B [:var x]))))
         [:pair l r] (string "(" (print/tm* l) ", " (print/tm* r) ")")
         [:fst p] (string "fst " (tm-arg p))
         [:snd p] (string "snd " (tm-arg p))
         [:t-id A x y] (string "Id " (tm-arg A) " " (tm-arg x) " " (tm-arg y))
         [:t-refl x] (string "refl " (tm-arg x))
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
         _ (string/format "%v" tm))))

(defn- with-state [f]
  (let [saved-id state/fresh-id
        saved-map state/name-map
        saved-used state/used-names]
    (state/reset!)
    (def out (f))
    (set state/fresh-id saved-id)
    (set state/name-map saved-map)
    (set state/used-names saved-used)
    out))

(defn print/ne [ne]
  (with-state (fn [] (print/ne* ne))))

(defn print/nf [nf]
  (with-state (fn [] (print/nf* nf))))

(defn print/tm [tm]
  (with-state (fn [] (print/tm* tm))))

(defn print/sem [sem]
  (with-state
    (fn []
      (let [tag (if (tuple? sem) (get sem 0) 0)]
        (cond
          (= tag tt/T/Neutral) (print/ne (get sem 1))
          (= tag tt/T/Type) (print/nf (tt/lower (tt/ty/type 100) sem))
          (= tag tt/T/Pi) (print/nf (tt/lower (tt/ty/type 100) sem))
          (= tag tt/T/Sigma) (print/nf (tt/lower (tt/ty/type 100) sem))
          (= tag tt/T/Id) (print/nf (tt/lower (tt/ty/type 100) sem))
          (= tag tt/T/Refl) (string "refl " (print/sem (get sem 1)))
          (= tag tt/T/Pair) (string "(" (print/sem (get sem 1)) ", " (print/sem (get sem 2)) ")")
          true (string/format "%v" sem))))))

(def exports
  {:print/tm print/tm
   :print/nf print/nf
   :print/ne print/ne
   :print/sem print/sem})
