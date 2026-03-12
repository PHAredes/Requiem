(import /build/hamt :as h)
(import ../../src/coreTT :as c)

(var default-seed nil)

(defn seed/current []
  (if default-seed
    default-seed
    (let [raw (os/getenv "TEST_SEED")
          seed (if raw
                 raw
                 (string (* 1000000 (os/clock))))]
      (set default-seed seed)
      seed)))

(defn trials/current [fallback]
  (let [raw (os/getenv "TEST_TRIALS")]
    (if raw
      (scan-number raw)
      fallback)))

(defn rng [&opt seed]
  (math/rng (or seed (seed/current))))

(defn choose [rng xs]
  (xs (math/rng-int rng (length xs))))

(defn gen-level [rng &opt max-level]
  (math/rng-int rng (or max-level 3)))

(defn gen-univ [rng]
  [:type (gen-level rng 3)])

(defn gen-neutral-var [rng]
  [:var (string "x" (math/rng-int rng 1000))])

(defn gen-simple-type [rng]
  (choose rng @[
    [:type 0]
    [:type 1]
    [:type 2]
    [:t-pi [:type 0] (fn [_] [:type 0])]
    [:t-sigma [:type 0] (fn [_] [:type 0])]
  ]))

(defn gen-context-entry [rng]
  (let [name (string "x" (math/rng-int rng 1000))
        ty (gen-simple-type rng)]
    [name ty]))

(defn gen-typed-context [rng max-vars]
  (reduce (fn [Γ _]
            (let [[name ty] (gen-context-entry rng)]
              (h/put Γ name ty)))
          (h/new)
          (range (or max-vars 0))))

(defn gen-context-term [rng Γ]
  (let [keys (h/keys Γ)]
    (if (= 0 (length keys))
      (gen-univ rng)
      [:var (choose rng keys)])))

(defn mk-judgment-sample [ctx term type-tm &opt extras]
  (merge @{:ctx ctx :term term :type-tm type-tm} (or extras @{})))

(defn mk-closed-sample [tm type-tm &opt extras]
  (merge @{:term tm :type-tm type-tm} (or extras @{})))

(defn closed-sample/universe [rng]
  (let [lvl (gen-level rng 3)]
    (mk-closed-sample
      [:type lvl]
      [:type (inc lvl)]
      @{:kind :universe :value? true})))

(defn closed-sample/identity [rng]
  (let [lvl (gen-level rng 3)
        A [:type lvl]
        pi-ty [:t-pi A (fn [_] A)]]
    (mk-closed-sample
      [:lam (fn [x] x)]
      pi-ty
      @{:kind :identity :value? true})))

(defn closed-sample/constant [rng]
  (let [arg-lvl (gen-level rng 3)
        body-lvl (gen-level rng 3)
        A [:type (inc arg-lvl)]
        body [:type body-lvl]
        body-ty [:type (inc body-lvl)]
        pi-ty [:t-pi A (fn [_] body-ty)]]
    (mk-closed-sample
      [:lam (fn [_] body)]
      pi-ty
      @{:kind :constant :value? true :body body})))

(defn closed-sample/pair [rng]
  (let [left-lvl (gen-level rng 3)
        right-lvl (gen-level rng 3)
        left [:type left-lvl]
        right [:type right-lvl]
        A [:type (inc left-lvl)]
        B [:type (inc right-lvl)]
        sigma-ty [:t-sigma A (fn [_] B)]]
    (mk-closed-sample
      [:pair left right]
      sigma-ty
      @{:kind :pair :value? true :left left :right right})))

(defn closed-sample/refl [rng]
  (let [lvl (gen-level rng 3)
        witness [:type lvl]
        witness-ty [:type (inc lvl)]
        eq-ty [:t-id witness-ty witness witness]]
    (mk-closed-sample
      [:t-refl witness]
      eq-ty
      @{:kind :refl :value? true :witness witness})))

(defn closed-sample/pi-type [rng]
  (let [dom-lvl (gen-level rng 3)
        cod-lvl (gen-level rng 3)
        A [:type dom-lvl]
        B [:type cod-lvl]
        universe [:type (inc (max dom-lvl cod-lvl))]]
    (mk-closed-sample
      [:t-pi A (fn [_] B)]
      universe
      @{:kind :pi-type :value? true})))

(defn closed-sample/sigma-type [rng]
  (let [dom-lvl (gen-level rng 3)
        cod-lvl (gen-level rng 3)
        A [:type dom-lvl]
        B [:type cod-lvl]
        universe [:type (inc (max dom-lvl cod-lvl))]]
    (mk-closed-sample
      [:t-sigma A (fn [_] B)]
      universe
      @{:kind :sigma-type :value? true})))

(defn closed-sample/J-refl [rng]
  (let [A [:type 1]
        x [:type 0]
        motive (fn [y _p] [:t-id A x y])
        base [:t-refl x]]
    (mk-closed-sample
      [:t-J A x motive base x [:t-refl x]]
      [:t-id A x x]
      @{:kind :J-refl :value? false})))

(defn closed-sample/J-proof-sensitive [rng]
  (let [A [:type 1]
        x [:type 0]
        p [:t-refl x]
        motive (fn [y q] [:t-id [:t-id A x y] q q])
        base [:t-refl p]
        proof-ty [:t-id A x x]]
    (mk-closed-sample
      [:t-J A x motive base x p]
      [:t-id proof-ty p p]
      @{:kind :J-proof-sensitive :value? false})))

(defn reducible-sample/beta-id [rng]
  (let [arg-lvl (gen-level rng 3)
        arg [:type arg-lvl]
        A [:type (inc arg-lvl)]
        tm [:app [:lam (fn [x] x)] arg]]
    (mk-closed-sample
      tm
      A
      @{:kind :beta-id
        :contractum arg
        :value? false
        :normal-form? false})))

(defn reducible-sample/beta-const [rng]
  (let [arg-lvl (gen-level rng 3)
        body-lvl (gen-level rng 3)
        arg [:type arg-lvl]
        body [:type body-lvl]
        A [:type (inc arg-lvl)]
        body-ty [:type (inc body-lvl)]
        tm [:app [:lam (fn [_] body)] arg]]
    (mk-closed-sample
      tm
      body-ty
      @{:kind :beta-const
        :contractum body
        :argument arg
        :value? false
        :normal-form? false})))

(defn reducible-sample/fst [rng]
  (let [left-lvl (gen-level rng 3)
        right-lvl (gen-level rng 3)
        left [:type left-lvl]
        right [:type right-lvl]
        A [:type (inc left-lvl)]
        B [:type (inc right-lvl)]
        pair [:pair left right]
        tm [:fst pair]]
    (mk-closed-sample
      tm
      A
      @{:kind :fst
        :contractum left
        :pair pair
        :value? false
        :normal-form? false})))

(defn reducible-sample/snd [rng]
  (let [left-lvl (gen-level rng 3)
        right-lvl (gen-level rng 3)
        left [:type left-lvl]
        right [:type right-lvl]
        A [:type (inc left-lvl)]
        B [:type (inc right-lvl)]
        pair [:pair left right]
        tm [:snd pair]]
    (mk-closed-sample
      tm
      B
      @{:kind :snd
        :contractum right
        :pair pair
        :value? false
        :normal-form? false})))

(defn gen-closed-value [rng]
  ((choose rng @[
     closed-sample/universe
     closed-sample/identity
     closed-sample/constant
     closed-sample/pair
     closed-sample/refl
     closed-sample/pi-type
     closed-sample/sigma-type
    ]) rng))

(def gen-canonical-sample gen-closed-value)

(defn gen-inferable-sample [rng]
  ((choose rng @[
     closed-sample/universe
     closed-sample/refl
     closed-sample/pi-type
     closed-sample/sigma-type
     closed-sample/J-refl
     closed-sample/J-proof-sensitive
    ]) rng))

(def gen-inferable-closed-sample gen-inferable-sample)

(defn inferable-judgment/universe [rng]
  (let [sample (closed-sample/universe rng)]
    (mk-judgment-sample (h/new) (sample :term) (sample :type-tm) @{:kind :closed-universe})))

(defn inferable-judgment/refl [rng]
  (let [sample (closed-sample/refl rng)]
    (mk-judgment-sample (h/new) (sample :term) (sample :type-tm) @{:kind :closed-refl})))

(defn inferable-judgment/pi-type [rng]
  (let [sample (closed-sample/pi-type rng)]
    (mk-judgment-sample (h/new) (sample :term) (sample :type-tm) @{:kind :closed-pi-type})))

(defn inferable-judgment/sigma-type [rng]
  (let [sample (closed-sample/sigma-type rng)]
    (mk-judgment-sample (h/new) (sample :term) (sample :type-tm) @{:kind :closed-sigma-type})))

(defn inferable-judgment/variable [rng]
  (let [lvl (gen-level rng 3)
        x (string "x" (math/rng-int rng 1000))
        A [:type lvl]]
    (mk-judgment-sample
      (h/put (h/new) x (c/eval (h/new) A))
      [:var x]
      A
      @{:kind :ctx-var :name x})))

(defn inferable-judgment/application [rng]
  (let [lvl (gen-level rng 3)
        f (string "f" (math/rng-int rng 1000))
        a (string "a" (math/rng-int rng 1000))
        A [:type lvl]
        pi-tm [:t-pi A (fn [_] A)]
        Γ (-> (h/new)
              (h/put f (c/eval (h/new) pi-tm))
              (h/put a (c/eval (h/new) A)))]
    (mk-judgment-sample
      Γ
      [:app [:var f] [:var a]]
      A
      @{:kind :ctx-app :fn-name f :arg-name a})))

(defn inferable-judgment/fst [rng]
  (let [left-lvl (gen-level rng 3)
        right-lvl (gen-level rng 3)
        p (string "p" (math/rng-int rng 1000))
        A [:type left-lvl]
        B [:type right-lvl]
        sigma-tm [:t-sigma A (fn [_] B)]
        Γ (h/put (h/new) p (c/eval (h/new) sigma-tm))]
    (mk-judgment-sample
      Γ
      [:fst [:var p]]
      A
      @{:kind :ctx-fst :pair-name p})))

(defn inferable-judgment/snd [rng]
  (let [left-lvl (gen-level rng 3)
        right-lvl (gen-level rng 3)
        p (string "p" (math/rng-int rng 1000))
        A [:type left-lvl]
        B [:type right-lvl]
        sigma-tm [:t-sigma A (fn [_] B)]
        Γ (h/put (h/new) p (c/eval (h/new) sigma-tm))]
    (mk-judgment-sample
      Γ
      [:snd [:var p]]
      B
      @{:kind :ctx-snd :pair-name p})))

(defn inferable-judgment/equality-proof [rng]
  (let [lvl (gen-level rng 3)
        e (string "e" (math/rng-int rng 1000))
        witness [:type lvl]
        witness-ty [:type (inc lvl)]
        eq-tm [:t-id witness-ty witness witness]
        Γ (h/put (h/new) e (c/eval (h/new) eq-tm))]
    (mk-judgment-sample
      Γ
      [:var e]
      eq-tm
      @{:kind :ctx-eq :proof-name e})))

(defn inferable-judgment/J-refl [rng]
  (let [sample (closed-sample/J-refl rng)]
    (mk-judgment-sample (h/new) (sample :term) (sample :type-tm) @{:kind :closed-J-refl})))

(defn inferable-judgment/J-proof-sensitive [rng]
  (let [sample (closed-sample/J-proof-sensitive rng)]
    (mk-judgment-sample (h/new) (sample :term) (sample :type-tm) @{:kind :closed-J-proof-sensitive})))

(defn gen-inferable-judgment [rng]
  ((choose rng @[
     inferable-judgment/universe
     inferable-judgment/refl
     inferable-judgment/pi-type
     inferable-judgment/sigma-type
     inferable-judgment/variable
     inferable-judgment/application
     inferable-judgment/fst
     inferable-judgment/snd
     inferable-judgment/equality-proof
     inferable-judgment/J-refl
     inferable-judgment/J-proof-sensitive
   ]) rng))

(defn gen-reducible-sample [rng]
  ((choose rng @[
     reducible-sample/beta-id
     reducible-sample/beta-const
     reducible-sample/fst
     reducible-sample/snd
   ]) rng))

(defn gen-closed-sample [rng]
  (if (= 0 (math/rng-int rng 2))
    (gen-canonical-sample rng)
    (gen-reducible-sample rng)))

(def gen-fragment-sample gen-closed-sample)

(defn gen-beta-redex [rng]
  (gen-reducible-sample rng))

(defn gen-fst-redex [rng]
  (reducible-sample/fst rng))

(defn gen-snd-redex [rng]
  (reducible-sample/snd rng))

(defn gen-convertible-pair [rng]
  (let [sample (gen-reducible-sample rng)]
    @{:term (sample :term)
      :contractum (sample :contractum)
      :type (sample :type-tm)
      :kind (sample :kind)}))

(defn gen-diamond [rng]
  (let [arg-lvl (gen-level rng 3)
        arg [:type arg-lvl]
        A [:type (inc arg-lvl)]
        inner [:app [:lam (fn [y] y)] arg]
        term [:app [:lam (fn [x] x)] inner]
        left [:app [:lam (fn [x] x)] arg]
        right inner]
    @{:term term
      :left left
      :right right
      :join arg
      :type A
      :kind :beta-beta}))

(defn gen-reduction-diamond [rng]
  (gen-diamond rng))

(defn gen-well-typed-sample [rng]
  (let [sample (gen-closed-sample rng)]
    @{:term (sample :term)
      :type (sample :type-tm)
      :kind (sample :kind)}))

(defn gen-nested-term [rng depth]
  (if (<= depth 0)
    (let [sample (gen-closed-sample rng)]
      (sample :term))
    (let [sample (gen-reducible-sample rng)
          value-sample (gen-closed-value rng)]
      (case (math/rng-int rng 4)
        0 (value-sample :term)
        1 (sample :term)
        2 [:pair (gen-nested-term rng (dec depth)) (value-sample :term)]
        3 [:app [:lam (fn [x] x)] (gen-nested-term rng (dec depth))]))))
