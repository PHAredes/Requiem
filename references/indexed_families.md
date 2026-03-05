# Indexed Families

Converted from `indexed_families.pdf` using `pdftotext` with light paragraph cleanup.

TWO TRICKS TO TRIVIALIZE HIGHER-INDEXED FAMILIES

arXiv:2309.14187v2 [cs.LO] 30 Oct 2023

TESLA ZHANG October 31, 2023 Abstract. The conventional general syntax of indexed families in dependent type theories follow the style of “constructors returning a special case”, as in Agda, Lean, Idris, Coq, and probably many other systems. Fording is a method to encode indexed families of this style with index-free inductive types and an identity type. There is another trick that merges interleaved higher inductive-inductive types into a single big family of types. It makes use of a small universe as the index to distinguish the original types. In this paper, we show that these two methods can trivialize some very fancylooking indexed families with higher inductive indices (which we refer to as higher indexed families).

Contents
## 1. Motivation
## 2. The peculiar deﬁnition of integers
## 3. Relation to circle
## 4. Fording indexed families
## 5. Further discussion on syntax
References

## 2
## 3
## 5
## 6
## 8
## 8

In this article, we show that the idea of Fording proposed by Conor McBride in [1] makes the “mini-universe” deﬁnition of integers Z𝑈 in [2] trivial. Warning 0.1. This is a very syntax-minded article, so there will be pseudocode snippets to provide intuition based on imaginary syntax, but those will be mostly analogous to the style in the HoTT book [3] and Cubical Agda [4].

A

We will also use the Aya language, which adapts a “pattern matching” syntax [5] for indexed families. For instance, the traditional deﬁnition of sized vectors looks like the following: open data Vec (A : Type) (n : Nat) | A, zero ⇒ nil | A, suc n ⇒ cons A (Vec A n) It says that “the type Vec has two constructors, nil is only available when the second argument of Vec is zero, and similarly for cons but only when it’s suc 𝑛”. The arguments of the constructors are listed like in Haskell, and unlike the GADT
## 1

## 2

TESLA ZHANG

syntax adapted in Haskell GADT [6], Agda [7], and Idris, we do not write out the return type of constructors. This pattern matching does not need to be exhaustive and can have redundant cases, because they are actually not pattern matching, but instead describes the availability of constructors. This syntax enjoys many beneﬁts compared to the traditional one, discussed in [5].
## 1. Motivation
The deﬁnition of Z𝑈 is said to be inspired from a trick due to Szumi Xie1, which is also seen in the Haskell parser generator BNFC2, where the --haskell-gadt option generates a big GADT that combines several data types in the following way: (1) Deﬁne an “enumeration” 𝑈, say, a data type with all constructors having no argument, (2) For every data type 𝐷, add a constructor 𝐷𝑈 to 𝑈, (3) Deﬁne a GADT 𝑇 indexed by 𝑈, say, 𝑇 : 𝑈 → 𝒰, (4) For every constructor 𝑐 : 𝑋 → 𝐷, add the following constructor to 𝑇: 𝑐𝑇 : 𝑋 → 𝑇 𝐷𝑈 Demonstration 1.1. Suppose we have the following data types, written in Haskell: data D1 = con1 Int | con2 Bool data D2 = con3 Bool | con4 Int By applying the trick, we get the following GADT: data U = D1_U | D2_U data T : (u : U) → Type where con1 _T : Int → T D1_U con2 _T : Bool → T D1_U con3 _T : Bool → T D2_U con4 _T : Int → T D2_U



Szumi Xie’s trick is essentially the same thing but applied to higher inductiveinductive types, so we can encode interleaved recursion among constructors with an indexed higher inductive type. This pattern is very common in the formalization of dependent type theory itself in dependent type theory. So, relating this inspired deﬁnition with something else could potentially open up a broader view of the trick, especially in homotopy type theory or dependent type theories with quotient inductive types [8]. We start from an explanation of Z𝑈 assuming familiarity with basic ideas in homotopy type theory [3], including univalence, the notion of equivalence (a function with the property of being an equivalence), and higher inductive types (chapter 6 of [3]). These will be used as the context of discussion, but we will not go into details, so even a vague impression should suﬃce. Then we explain the Fording technique, and show how to Ford Z𝑈 . 1Used in https://bitbucket.org/szumixie/tt-in-tt/src/master/Cubical/Syntax.agda, a formalization of type theory syntax in Cubical Agda [4]
## 2Website: https://bnfc.digitalgrammars.com, GitHub: https://github.com/BNFC/bnfc

TWO TRICKS TO TRIVIALIZE HIGHER-INDEXED FAMILIES

## 3

## 2. The peculiar definition of integers
In [2], Thorsten Altenkirch and Luis Scoccola proposed the following deﬁnition of integers using a “mini-universe”: open data U | T | path : T = T open data PreInt U | T ⇒ zero def Int ⇒ PreInt T They call it Z𝑈 , but we stick to an ASCII name for a controlled use of Unicode characters in program source code. This deﬁnition is not expected to the understood just by looking at it – the rest of this section is devoted to provide the relevant background. Remark 2.1. In the above snippet, PreInt is a simpler indexed type [5]. It is equivalent to the following Agda-style constructor: zero : PreInt T

To decipher this deﬁnition, we need to understand what integers are. Instead of just deﬁning the sets (i.e. list its elements) or the normal form of integers, we look at the algebraic structure. We think of them as a modiﬁed version of natural numbers, where the successor function is not just a constructor (which is an injective map), but is also equipped with a “canonical inverse” (so it’s now bĳective), so it becomes an equivalence rather than a function. So, it is tempting to write down the following deﬁnition: data Int where zero : Int succ : Int ≃ Int How do we deal with elimination of this type? Observation 2.2. Maps from a natural number to 𝑋 always provide the following information: • An instance 𝑥 : 𝑋, • A function 𝑓 : 𝑋 → 𝑋. This is because every map ℎ from a natural number to 𝑋 consists of: • ℎ(0), which is an instance of 𝑋, • ℎ(𝑛 + 1), which can use ℎ(𝑛) : 𝑋 and constructs an instance of 𝑋, which is essentially a map from 𝑋 to 𝑋. Maps from an integer, analogously, always provide the following information: • An instance 𝑥 : 𝑋, • An equivalence 𝑒 : 𝑋 ≃ 𝑋. This is what we need to provide in the eliminator!

E

## 4

TESLA ZHANG

But the above imaginary syntax is not supported by any known type theory (which may also worth exploration!). One way to make sense of this is to unfold the deﬁnition of equivalence, which is discussed in detail in [2]. Observation 2.3. For the deﬁnition of Z𝑈 , we may apply PreInt to path to get the analogous thing of succ as in observation 2.2: def succPath : Int ↑ = Int ⇒ ap PreInt path The ↑ symbol lifts the = to a higher universe level, so we can put types on the two sides of a path.3 It is harmless in this particular case to just ignore it. The design follows Conor McBride’s proposal of implementing universe polymorphism, studied in [9].

E E

Observation 2.4. The equivalence in observation 2.3 gives the successor and predecessor function on integers, as well as the fact that they are inverse to each other. The other way is to think about Szumi Xie’s trick. When we want to deﬁne 𝑛 separate types, we can deﬁne one type indexed by an enumeration of 𝑛 constructors. The enumeration is considered a “mini-universe”, as it governs several types. Now we want to deﬁne a type Int with an equivalence on itself, so instead we deﬁne a type indexed by a “higher-enumeration” U with two constructors: • Int for the type we want to deﬁne, • path of type Int = Int for the equivalence on the type itself. We work with path instead of the actual equivalence deﬁnition because only the former is supported by higher inductive types. Then, the type indexed by U (we call it PreInt) will have some constructors that correspond to the constructors of Int. For zero, we add zero𝑇 : PreInt 𝑇 And the good news is that we don’t need to do anything for succ, because we can directly derive it from path induction on path. Assuming the following operator for substitution and path reversal (implementation omitted to avoid distraction): def subst (P : A → Type) {a b : A} (p : a = b) : P(a) → P(b) def sym {a b : A} (p : a = b) : b = a We can deﬁne the functions succ and even pred as follows: def succ : Int → Int ⇒ subst PreInt path def pred : Int → Int ⇒ subst PreInt (sym path) Note that succ is just the underlying function of the map in observation 2.3. We may also show that they’re inverse to each other, because substitution commutes with path composition, say, we have the following path equivalences: subst 𝐴 𝑝 (subst 𝐴 𝑞 𝑢) = subst 𝐴 (𝑝 · 𝑞) 𝑢 subst 𝐴 idp 𝑢 = 𝑢 These lemmas directly leads to the desired results. Remark 2.5. In cubical type theory one can try to write this: succ𝑇 : (𝑖 : I) → PreInt (path 𝑖)
## 3Ideally, this should be inferred automatically, but we haven’t implemented it yet.

TWO TRICKS TO TRIVIALIZE HIGHER-INDEXED FAMILIES

## 5

It is diﬃcult to make sense of this thing at this point, because the boundary information needs to be taken care of, and we do not yet know where this should happen. This will be addressed later.

## 3. Relation to circle
Observe that the deﬁnition T is identical to the circle 𝑆 1 , so we can rewrite the above deﬁnition with some renamings: open data S1 | base | loop : base = base open data Helix S1 | base ⇒ zero def Int ⇒ Helix base In essence, this deﬁnition of integers is directly related to the path space of 𝑆 1 . To make sense of this, we ﬁrst refer to the famous theorem in homotopy type theory [10]: (base = base) ≃ Z The proof is by showing that, for 𝑥 : 𝑆 1 , the following type applied by 𝑥 is equivalent to the path space of 𝑆 1 based at 𝑥: def Code S1 : Type | base ⇒ Z | loop i ⇒ univalence succEquiv i And the two directions of the theorem are called encode and decode respectively: encode : (𝑥 : 𝑆 1 ) → (base = 𝑥) → Code(𝑥) decode : (𝑥 : 𝑆 1 ) → Code(𝑥) → (base = 𝑥) The fact that encode and decode are inverses of each other can be illustrated in the following way: • The base point corresponds to Code(base) ≡ Z: Z • base • • The loop corresponds to the path obtained from applying succEquiv to univalence: • univalence succEquiv 𝑖 Z • base •

• loop 𝑖

Remark 3.1. We have omitted the following deﬁnition for spatial considerations4: • Z is the type of integers. This is not to be confused with Int, which is a concrete deﬁnition given above. Here Z can be any deﬁnition of integers, preferably a simple, intuitive one. • succ is the successor function on Z. Every integer type should have such a function.
## 4In fact, we haven’t ﬁnish implementing univalence in Aya yet.

## 6

TESLA ZHANG

• succEquiv is an equivalence between Z and itself, given by succ. • univalence takes an equivalence and returns a path. Another purpose of this emission is to encourage readers to think about integers abstractly. Also, Aya uses the cubical deﬁnition of path, which is similar to a function from the interval type. That’s also why the pattern for loop has a parameter. Curious

readers can refer to [11] for more details. Observation 3.2. In the deﬁnition of Code, we put Z and an equivalence on itself that corresponds to succ to the function bodies. As observed in observation 2.2, this is the essential information we want on integers. By encode-decode of 𝑆 1 , we know that Code is equivalent to the path space of
## 1
𝑆 . So, if somehow we can make the path space of 𝑆 1 as the definition of integers, then it will be really nice.

E

## 4. Fording indexed families
Henry Ford is quoted for having said that “Any color the customer wants, as long as it’s black.” An analogous method is used to encode indexed families with a built-in identity type: suppose we have a family 𝐹 : 𝐴 → 𝒰 with a constructor 𝑐 : 𝑋 → 𝐹 𝑎 for some expression 𝑎 : 𝐴 (usually in neutral form), Fording turns it into the following: 𝑐Ford : (𝑎 ′ : 𝐴) → (𝑎 = 𝑎 ′) → 𝑋 → 𝐹 𝑎 ′ And now 𝐹 is no longer indexed. Demonstration 4.1. Consider the following indexed family: open data Bool | true | false open data So Bool | true ⇒ oh We have: • oh : So true is the unique inhabitant, • So false is the empty type. This type is extensively used in the Idris language (as Data.So 5), where it lifts any Boolean-valued test to a type-level proposition. Fording it gives us the following type: open data So (b : Bool) | oh (b = true) Then we can see directly that So 𝑏 is nothing but a wrapper of 𝑏 = true.



Exercise 4.2. Ford the standard deﬁnition of ﬁnite sets (called Fin in Idris) and the sized vector type. Fording helps us get rid of index uniﬁcation in pattern matching. Suppose we want to split on the type 𝐹 𝑏 for some 𝑏 : 𝐴, then if we write the pattern 𝑐 𝑥, it must be the case that 𝑏 and 𝑎 can be unified, otherwise this pattern matching will
## 5https://www.idris-lang.org/docs/idris2/current/base_docs/docs/Data.So.html

TWO TRICKS TO TRIVIALIZE HIGHER-INDEXED FAMILIES

## 7

be rejected. In case 𝑏 is a function call that stuck on some argument, this uniﬁcation is very unlikely to succeed. Demonstration 4.3. We cannot perform pattern matching on a type So (isEmpty 𝑥) where 𝑥 : List 𝐴 is a variable.



Remark 4.4. In traditional dependent pattern matching [12], writing oh as a pattern for the type So 𝑥 (when 𝑥 is a variable) will rewrite 𝑥 as true in the right-hand side of the clause: f : (x : Bool) → So x → x = true f _ oh = reﬂ We assume reﬂ to be the constructor of the inductively-deﬁned identity type. This is a desirable feature because it matches the intuition that “only when 𝑥 is true can we construct oh as a proof of So 𝑥”. After Fording, we can do the same by writing oh reﬂ: f : (x : Bool) → So x → x = true f _ (oh reﬂ) = reﬂ But what’s good about Fording is that we can delay this rewriting to the moment when we actually need it, especially in case 𝑥 is not a variable. In fact, in the above case, we don’t even do any dependent pattern matching: f : (x : Bool) → So x → x = true f _ (oh p) = p This also prevents over-eager rewriting of variables, which can potentially lead to unreadable compiler output when doing type-directed development, or slow down proof search.

Now, let’s apply this to the deﬁnition of integers: open data S1 | base | loop : base = base open data Helix (x : S1 ) | zero (x = base) def Int ⇒ Helix base

E E

Observation 4.5. The type Helix is simply a wrapper of the path space of 𝑆 1 based at a point given by the parameter 𝑥 : 𝑆 1 .

Observation 4.6. The type Int, when we look through the wrapper Helix, is an alias to the type base = base. The same idea applies to any inhabited type. Consider such a case h𝐻 : 𝒰 , 𝑥 : 𝐻i. The path space of 𝐻 based at 𝑥 : 𝐻 can be deﬁned as 𝑃 : 𝐻 → 𝒰 with a constructor 𝑐 : 𝑃 𝑥. Fording also reveals the mystery behind the constructor succ𝑇 in remark 2.5 by expanding it to: open data Helix’ (x : S1 ) | zero (x = base) | succ (i : I) (x = loop i) And we know how to read this type in cubical type theory: it’s a square!

## 8

TESLA ZHANG

𝑥

•

𝑖

path 𝑥

•

So the constructor is just parameterized by a square in a peculiar way.
## 5. Further discussion on syntax
In observation 2.2, we have given an example of type that is freely generated by a constructor and an equivalence on the type, where the equivalence is a constructor equipped with the property of being an equivalence (called isEquiv in various formalization projects). Even though this can only be expressed by expanding the deﬁnition of equivalence and will end up giving us loads of constructors, it is a powerful notation for informal writings. Demonstration 5.1. A real-world use case is in [13, §2], which cites a result from [14] that certain path space of pushout is freely generated by reﬂexivity and an equivalence. The pushout discussed in the paper is deﬁned for a span, which includes 𝐴 : 𝒰 , 𝐵 : 𝒰 , 𝑅 : 𝐴 → 𝐵 → 𝒰, and we write 𝐴 +𝑅 𝐵 for the pushout, and inl : 𝐴 → 𝐴 +𝑅 𝐵 inr : 𝐵 → 𝐴 +𝑅 𝐵 as two of its constructors. The path spaces of interest are: inl(𝑎0 ) = inl(𝑎)

inl(𝑎0 ) = inr(𝑏)

inr(𝑏) = inr(𝑏 ′)

And the constructors for these types are: data PathSpaces (A B : Type) (R : A → B → Type) where reﬂ : (a0 : A) → inl(a0 ) = inl(a0 ) eq : (a0 a : A) → (b : B) → R a b → (inl(a0 ) = inl(a)) ≃ (inl(a0 ) = inr(b)) Without homotopy type theory, it should be quite diﬃcult to describe this path space, and even if it’s written by someone, it’s less likely to be understood by others compared to this one.



References [1] James Chapman, Pierre-Évariste Dagand, Conor McBride, and Peter Morris. “The Gentle Art of Levitation”. In: Proceedings of the 15th ACM SIGPLAN International Conference on Functional Programming. ICFP ’10. Baltimore, Maryland, USA: Association for Computing Machinery, 2010, pp. 3–14. isbn:
## 9781605587943. doi: 10.1145/1863543.1863547.
[2] Thorsten Altenkirch and Luis Scoccola. “The Integers as a Higher Inductive Type”. In: CoRR abs/2007.00167 (2020). arXiv: 2007.00167. url: https:// arxiv.org/abs/2007.00167. [3] The Univalent Foundations Program. Homotopy Type Theory: Univalent Foundations of Mathematics. Institute for Advanced Study: https://homotopytypetheory. org/book, 2013.

REFERENCES

## 9

[4] Andrea Vezzosi, Anders Mörtberg, and Andreas Abel. “Cubical Agda: A Dependently Typed Programming Language with Univalence and Higher Inductive Types”. In: Proc. ACM Program. Lang. 3.ICFP (July 2019). doi:
## 10.1145/3341691.
[5] Tesla Zhang. “A Simpler Encoding of Indexed Types”. In: Proceedings of the 6th ACM SIGPLAN International Workshop on Type-Driven Development. TyDe ’21. Republic of Korea: ACM, 2021. isbn: 978-1-4503-8616-6. doi: 10.1145/3471875.3472991. arXiv: 2103.15408. [6] Dimitrios Vytiniotis, Stephanie Weirich, and Simon Peyton Jones. “Simple uniﬁcation-based type inference for GADTs”. In: International Conference on Functional Programming (ICFP’06). 2016 ACM SIGPLAN Most Inﬂuential ICFP Paper Award. ACM SIGPLAN. Apr. 2006. url: https://www. microsoft.com/en-us/research/publication/simple-unification-basedtype-inference-for-gadts/. [7] Ulf Norell. “Dependently Typed Programming in Agda”. In: Proceedings of the 4th International Workshop on Types in Language Design and Implementation. TLDI ’09. Savannah, GA, USA: ACM, 2009, pp. 1–2. isbn: 978-1-60558-420-1. doi: 10.1145/1481861.1481862. [8] Thorsten Altenkirch, Paolo Capriotti, Gabe Dĳkstra, Nicolai Kraus, and Fredrik Nordvall Forsberg. “Quotient inductive-inductive types”. In: Foundations of Software Science and Computation Structures: 21st International Conference, FOSSACS 2018, Held as Part of the European Joint Conferences on Theory and Practice of Software, ETAPS 2018, Thessaloniki, Greece, April 14–20, 2018. Proceedings 21. Springer International Publishing. 2018, pp. 293–310. [9] Kuen-Bang Hou (Favonia), Carlo Angiuli, and Reed Mullanix. “An OrderTheoretic Analysis of Universe Polymorphism”. In: Proc. ACM Program. Lang.
## 7.POPL (Jan. 2023). doi: 10.1145/3571250. url: https://doi.org/10.1145/
## 3571250.
[10] Daniel R. Licata and Michael Shulman. “Calculating the Fundamental Group of the Circle in Homotopy Type Theory”. In: (2013). arXiv: 1301.3443 [math.LO]. [11] Thierry Coquand, Simon Huber, and Anders Mörtberg. “On Higher Inductive Types in Cubical Type Theory”. In: Proceedings of the 33rd Annual ACM/IEEE Symposium on Logic in Computer Science. LICS ’18. Oxford, United Kingdom: Association for Computing Machinery, 2018, pp. 255–264. isbn:
## 9781450355834. doi: 10.1145/3209108.3209197.
[12] Jesper Cockx. “Dependent Pattern Matching and Proof-Relevant Uniﬁcation”. PhD thesis. KU Leuven, 2017. [13] David Wärn. “Path Spaces of Pushouts”. In: (Aug. 2023). url: https:// dwarn.se/po-paths.pdf. [14] Nicolai Kraus and Jakob von Raumer. “Path Spaces of Higher Inductive Types in Homotopy Type Theory”. In: (2019). arXiv: 1901.06022 [math.LO]. Carnegie Mellon University Email address: teslaz@cmu.edu
