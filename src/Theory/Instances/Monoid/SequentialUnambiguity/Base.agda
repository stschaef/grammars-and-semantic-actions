{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Sequential unambiguity.

   `A ⊛ B` says: for every character, either `A` cannot be *continued* by it
   or `B` cannot *begin* with it.  That is exactly the condition under which
   a concatenation `A ⊗ B` has at most one splitting -- the reason it is the
   side condition every LL/greedy argument wants.

   The combinators below are all `Sum.map` over `First`/`FollowLast`; the
   content is in those files. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.SequentialUnambiguity.Base
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Relation.Nullary.Base using (Discrete ; yes ; no)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Bool using (Bool ; true ; false)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List as L using (List ; [] ; _∷_)
open import Cubical.Data.Sigma

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⊗ε-unit-l⁻)
open import Theory.Instances.Monoid.Precise Alphabet isSetAlphabet using (flat)
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (&⊕ᴰ-distR ; ⊗⊕ᴰ-distL ; ⊗⊕ᴰ-distR ; &⊕-distR ; ⊗ε-unit-r)
open import Theory.Instances.Monoid.Precise Alphabet isSetAlphabet
  using (⊗&-align)
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet
  using (NIL ; CONS)
open import Theory.Instances.Monoid.Convolution Alphabet isSetAlphabet
  using (⟦⊗e⟧ ; ⊗e-ε→)
open import Theory.Instances.Monoid.SequentialUnambiguity.FollowLast
  Alphabet isSetAlphabet public

private variable ℓA ℓB ℓC ℓD : Level

sequentiallyUnambiguous :
  TheoryTy ℓA tt → TheoryTy ℓB tt → Type _
sequentiallyUnambiguous A B =
  (c : Alphabet) → (c ∉FollowLast A) Sum.⊎ (c ∉First B)

syntax sequentiallyUnambiguous A B = A ⊛ B

-- transport along maps, in either argument
⊛∘⊢-r : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → A ⊛ B → C ⊢ B → A ⊛ C
⊛∘⊢-r sep f c = Sum.map (λ x → x) (∉First∘⊢ f) (sep c)

⊛∘⊢-l : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → A ⊛ B → C ⊢ A → C ⊛ B
⊛∘⊢-l sep f c = Sum.map (∉FollowLast∘⊢ f) (λ x → x) (sep c)

-- ...and through each connective on the right
⊛-⊗l : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → A ⊛ B → ¬Nullable B → A ⊛ (B ⊗ C)
⊛-⊗l sep nu c = Sum.map (λ x → x) (∉First⊗l nu) (sep c)

⊛-⊗ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → A ⊛ B → A ⊛ C → A ⊛ (B ⊗ C)
⊛-⊗ sepB sepC c =
  Sum.rec Sum.inl
    (λ hB → Sum.rec Sum.inl (λ hC → Sum.inr (∉First⊗ hB hC)) (sepC c))
    (sepB c)

⊛-⊕ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → A ⊛ B → A ⊛ C → A ⊛ (B ⊕ C)
⊛-⊕ sepB sepC c =
  Sum.rec Sum.inl
    (λ hB → Sum.rec Sum.inl (λ hC → Sum.inr (∉First-⊕ hB hC)) (sepC c))
    (sepB c)

⊛-& : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → A ⊛ B → A ⊛ (B & C)
⊛-& sep = ⊛∘⊢-r sep π₁

⊛-* : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} → A ⊛ B → A ⊛ (B *)
⊛-* sep c = Sum.map (λ x → x) ∉First* (sep c)

⊛-⊥ : {A : TheoryTy ℓA tt} → A ⊛ (⊥Ty {s = tt})
⊛-⊥ c = Sum.inr ∉First-⊥

-- ε is sequentially unambiguous with everything, on either side: it has no
-- last character to follow and no first character to begin with.
⊛-εL : {A : TheoryTy ℓA tt} → εTy ⊛ A
-- `c ∉FollowLast εTy` unfolds to `¬Nullable (εTy ⊗ startsWith c)`
⊛-εL c = Sum.inl (⊗-¬NullableR ¬Nullable-startsWith)

⊛-εR : {A : TheoryTy ℓA tt} → A ⊛ εTy
⊛-εR c = Sum.inr ∉First-ε

-- If `c` cannot follow `A`, then `A` is sequentially unambiguous with
-- anything beginning with `c`: any other character cannot begin it.
module _ {A : TheoryTy ℓA tt} (c : Alphabet)
  (h : c ∉FollowLast A) (disc : Discrete Alphabet) where

  ∉FollowLast→⊛ : A ⊛ startsWith c
  ∉FollowLast→⊛ c' with disc c c'
  ... | yes p = Sum.inl (subst (_∉FollowLast A) p h)
  ... | no ¬p = Sum.inr (lit-first-clash c' c (λ q → ¬p (sym q)))
    where
    -- two different characters cannot both head the same word
    lit-first-clash : (d e : Alphabet) → (d ≡ e → Empty.⊥)
      → d ∉First (startsWith e)
    lit-first-clash d e ne m (sw , sw') =
      Empty.rec (ne (headEq m sw sw'))
      where
      headEq : (m : String) → startsWith d m → startsWith e m → d ≡ e
      headEq m (ms , q , (ld , _)) (ns , q' , (le , _)) =
        L.cons-inj₁
          (flat d (ms zero) (ms (suc zero)) m ld q
           ∙ sym (flat e (ns zero) (ns (suc zero)) m le q'))

-- The right factor's first character, made explicit.
¬Null→⊕first : {B : TheoryTy ℓB tt}
  → ¬Nullable B → B ⊢ ⊕[ c ∈ Alphabet ] (B & startsWith c)
¬Null→⊕first nu =
  &⊕ᴰ-distR ∘⊢ (id⊢ ,& (char⁺→⊕startsWith ∘⊢ ¬Nullable→char⁺ nu))

-- ...and `⊤Ty` on the right of a `startsWith` is absorbed.
startsWith⊗⊤ : {c : Alphabet} → startsWith c ⊗ ⊤Ty ⊢ startsWith c
startsWith⊗⊤ = ⊗-map id⊢ ⊤Ty-intro ∘⊢ ⊗-assoc

-- The point of `⊛`: if `A` is sequentially unambiguous with a non-nullable
-- `B`, then an `A`-word cannot also be an `A` followed by a `B` followed by
-- anything.  Whichever side the separation refuses `B`'s first character
-- to, that side gives the contradiction.
⊛→must-split : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → A ⊛ B → ¬Nullable B → disjoint A (A ⊗ B ⊗ ⊤Ty)
⊛→must-split {A = A} {B = B} sep nu =
  ⊕ᴰ-elim (λ c → Sum.rec
      (λ hFL → hFL ∘⊢ ((⊗-map id⊢ (startsWith⊗⊤ {c = c}
                          ∘⊢ ⊗-map (π₂ {A = B} {B = startsWith c}) id⊢)
                        ∘⊢ π₂) ,& π₁))
      (λ hF → ⊗⊥-annihR {C = A}
              ∘⊢ ⊗-map id⊢ (⊗⊥-annihL {C = ⊤Ty}
                            ∘⊢ ⊗-map (hF ∘⊢ &-swap {A = B} {B = startsWith c})
                                     (id⊢ {A = ⊤Ty}))
              ∘⊢ π₂)
      (sep c))
  ∘⊢ &⊕ᴰ-distR
  ∘⊢ (π₁ ,& (⊗⊕ᴰ-distR ∘⊢ ⊗-map id⊢ (⊗⊕ᴰ-distL ∘⊢ ⊗-map (¬Null→⊕first nu) id⊢)
             ∘⊢ π₂))

-- `⊕` on the left of a `&`, the mirror of `⊕-elim&`.
private
  ⊕-elim&L : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
    {C : TheoryTy ℓC tt} {D : TheoryTy ℓD tt}
    → A & D ⊢ B → C & D ⊢ B → (A ⊕ C) & D ⊢ B
  ⊕-elim&L f g = ⊕-elim& (f ∘⊢ &-swap) (g ∘⊢ &-swap) ∘⊢ &-swap

-- The keystone.  Two ways of reading one word as `A` followed by something
-- must cut it in the same place, because the letter at which the two cuts
-- differ would have to both follow `A` and open the right factor.  This is
-- `Precise.⊗&-align`; the old proof went through the external splitting
-- trichotomy and two four-fold `⊕ᴰ-elim`s.
⊗&-distL : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → A ⊛ B → A ⊛ C → (A ⊗ B) & (A ⊗ C) ⊢ (A & A) ⊗ (B & C)
⊗&-distL {A = A} {B = B} {C = C} sepB sepC =
  ⊗&-align {A = A} {B = B} {C = A} {D = C} sepB sepC

⊗&-distL⁻ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → (A & A) ⊗ (B & C) ⊢ (A ⊗ B) & (A ⊗ C)
⊗&-distL⁻ = ⊗-map π₁ π₁ ,& ⊗-map π₂ π₂

-- ...and at three factors, which is the shape the star argument wants.
factor⊗3 : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  {C : TheoryTy ℓC tt} {D : TheoryTy ℓD tt}
  → A ⊛ B → ¬Nullable B
  → (A ⊗ (B ⊗ C)) & (A ⊗ (B ⊗ D)) ⊢ (A & A) ⊗ ((B ⊗ C) & (B ⊗ D))
factor⊗3 sep nu = ⊗&-distL (⊛-⊗l sep nu) (⊛-⊗l sep nu)

-- Closure of `∉FollowLast` under the connectives.

-- With `B` non-nullable the `c` is `B`'s business alone: the separation
-- pins the cut, and `c ∉FollowLast B` finishes.
∉FollowLast-⊗¬null : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {c : Alphabet}
  → ¬Nullable B → A ⊛ B → c ∉FollowLast B → c ∉FollowLast (A ⊗ B)
∉FollowLast-⊗¬null nu sep h =
  ⊗⊥-annihR
  ∘⊢ ⊗-map id⊢ h
  ∘⊢ ⊗&-distL (⊛-⊗l sep nu) sep
  ∘⊢ (⊗-assoc ,&p id⊢)

-- If `B` may be empty, split on whether it is.  Empty: the `c` follows `A`
-- directly, so `c ∉First B` refutes it after `∉FollowLast→⊛` pins the cut.
-- Nonempty: replace `B` by `B & char⁺` and split again on the *other*
-- copy of `B` -- empty there is `⊛→must-split`, nonempty is the previous
-- lemma.
module _ {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {c : Alphabet}
  (sep : A ⊛ B) (hFLA : c ∉FollowLast A) (hFLB : c ∉FollowLast B)
  (hFB : c ∉First B) (disc : Discrete Alphabet) where

  private
    sep⁺ : A ⊛ (B & char⁺)
    sep⁺ = ⊛-& sep

    hFLB⁺ : c ∉FollowLast (B & char⁺)
    hFLB⁺ = ∉FollowLast∘⊢ π₁ hFLB

    -- `B` empty: the `c` is the one that follows `A`
    emptyB : (A ⊗ ((B & εTy) ⊗ startsWith c)) & (A ⊗ B) ⊢ ⊥Ty
    emptyB =
      ⊗⊥-annihR
      ∘⊢ ⊗-map id⊢ hFB
      ∘⊢ ⊗&-distL (∉FollowLast→⊛ c hFLA disc) sep
      ∘⊢ ((⊗-map (⊗ε-unit-r ∘⊢ ⊗-map id⊢ π₂) id⊢ ∘⊢ ⊗-assoc⁻) ,&p id⊢)

    -- ...and the other copy of `B` is empty, so the whole `c`-suffix sits
    -- past a complete `A`
    tailEmpty : (A ⊗ ((B & char⁺) ⊗ startsWith c)) & (A ⊗ (B & εTy)) ⊢ ⊥Ty
    tailEmpty =
      ⊛→must-split sep⁺ ¬Nullable-&char⁺
      ∘⊢ ((⊗ε-unit-r ∘⊢ ⊗-map id⊢ π₂ ∘⊢ π₂)
          ,& (⊗-map id⊢ (⊗-map id⊢ ⊤Ty-intro) ∘⊢ π₁))

    tailNonempty : (A ⊗ ((B & char⁺) ⊗ startsWith c)) & (A ⊗ (B & char⁺))
                 ⊢ ⊥Ty
    tailNonempty =
      ∉FollowLast-⊗¬null ¬Nullable-&char⁺ sep⁺ hFLB⁺ ∘⊢ (⊗-assoc⁻ ,&p id⊢)

    nonemptyB : (A ⊗ ((B & char⁺) ⊗ startsWith c)) & (A ⊗ B) ⊢ ⊥Ty
    nonemptyB =
      ⊕-elim& tailEmpty tailNonempty
      ∘⊢ (id⊢ ,&p (⊗⊕-distR {A = A} {B = B & εTy} {C = B & char⁺}
                   ∘⊢ ⊗-map id⊢ (stringSplit {A = B})))

  ∉FollowLast-⊗null : c ∉FollowLast (A ⊗ B)
  ∉FollowLast-⊗null =
    ⊕-elim&L emptyB nonemptyB
    ∘⊢ ((⊗⊕-distR {A = A} {B = (B & εTy) ⊗ startsWith c}
                  {C = (B & char⁺) ⊗ startsWith c}
         ∘⊢ ⊗-map id⊢ (⊗⊕-distL {A = B & εTy} {B = B & char⁺}
                                {C = startsWith c}
                       ∘⊢ ⊗-map (stringSplit {A = B}) id⊢)
         ∘⊢ ⊗-assoc) ,&p id⊢)

-- A `c` after an `A ⊕ B` either follows the summand it started, or crosses
-- from one to the other.  The crossing is refuted by `#`: the two summands
-- cannot share a first letter, and whichever of them cannot be empty
-- supplies the character to clash on.
module _ {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {c : Alphabet}
  (hFLA : c ∉FollowLast A) (hFLB : c ∉FollowLast B)
  (nuB∨hFA : (¬Nullable B) Sum.⊎ (c ∉First A))
  (nuA∨hFB : (¬Nullable A) Sum.⊎ (c ∉First B))
  (sep : A # B) where

  private
    crossBA : (B ⊗ startsWith c) & A ⊢ ⊥Ty
    crossBA = Sum.rec fromNull fromFirst nuB∨hFA
      where
      fromNull : ¬Nullable B → (B ⊗ startsWith c) & A ⊢ ⊥Ty
      fromNull nuB =
        #→disjoint (#⊗l ¬Nullable-&char⁺ (sym# (#∘⊢2 π₁ π₁ sep)))
                   (Sum.inl (¬Nullable⊗l ¬Nullable-&char⁺))
        ∘⊢ ((⊗-map (id⊢ ,& ¬Nullable→char⁺ nuB) id⊢ ∘⊢ π₁)
            ,& (π₂ ,& (¬Nullable→char⁺ (¬Nullable⊗l nuB) ∘⊢ π₁)))

      fromFirst : c ∉First A → (B ⊗ startsWith c) & A ⊢ ⊥Ty
      fromFirst hFA =
        ⊕-elim&L
          (hFA ∘⊢ ((⊗-unit-l ∘⊢ ⊗-map π₂ id⊢) ,&p id⊢))
          (#→disjoint (#⊗l ¬Nullable-&char⁺ (#∘⊢ π₁ (sym# sep)))
                      (Sum.inl (¬Nullable⊗l ¬Nullable-&char⁺)))
        ∘⊢ ((⊗⊕-distL ∘⊢ ⊗-map (stringSplit {A = B}) id⊢) ,&p id⊢)

    crossAB : (A ⊗ startsWith c) & B ⊢ ⊥Ty
    crossAB = Sum.rec fromNull fromFirst nuA∨hFB
      where
      fromNull : ¬Nullable A → (A ⊗ startsWith c) & B ⊢ ⊥Ty
      fromNull nuA =
        #→disjoint (#⊗l ¬Nullable-&char⁺ (#∘⊢2 π₁ π₁ sep))
                   (Sum.inl (¬Nullable⊗l ¬Nullable-&char⁺))
        ∘⊢ ((⊗-map (id⊢ ,& ¬Nullable→char⁺ nuA) id⊢ ∘⊢ π₁)
            ,& (π₂ ,& (¬Nullable→char⁺ (¬Nullable⊗l nuA) ∘⊢ π₁)))

      fromFirst : c ∉First B → (A ⊗ startsWith c) & B ⊢ ⊥Ty
      fromFirst hFB =
        ⊕-elim&L
          (hFB ∘⊢ ((⊗-unit-l ∘⊢ ⊗-map π₂ id⊢) ,&p id⊢))
          (#→disjoint (#⊗l ¬Nullable-&char⁺ (#∘⊢ π₁ sep))
                      (Sum.inl (¬Nullable⊗l ¬Nullable-&char⁺)))
        ∘⊢ ((⊗⊕-distL ∘⊢ ⊗-map (stringSplit {A = A}) id⊢) ,&p id⊢)

  ∉FollowLast-⊕ : c ∉FollowLast (A ⊕ B)
  ∉FollowLast-⊕ =
    ⊕-elim& (⊕-elim&L hFLA crossBA) (⊕-elim&L crossAB hFLB)
    ∘⊢ (⊗⊕-distL {A = A} {B = B} {C = startsWith c} ,&p id⊢)

-- Brüggemann-Klein and Wood's star theorem.  The `c` may sit arbitrarily
-- deep, so the refutation is a fold with carrier `¬Ty (FollowLastTy (A *) c)
-- & (A *)`; each cons step pins the two cuts with `⊗&-distL` twice.
module _ {A : TheoryTy ℓA tt} {c : Alphabet}
  (hFA : c ∉First A) (hFLA : c ∉FollowLast A)
  (sep : A ⊛ A) (disc : Discrete Alphabet) where

  private
    ⊛* : A ⊛ (A *)
    ⊛* = ⊛-* sep

    -- a nonempty `A *` is an `A` followed by an `A *`
    nonmt* : ((A *) & char⁺) ⊢ A ⊗ (A *)
    nonmt* =
      ⊕-elim&L π₁ (⊥Ty-elim ∘⊢ char⁺-¬Nullable ∘⊢ &-swap ∘⊢ (lowerTy ,&p id⊢))
      ∘⊢ (unroll* ,&p id⊢)

    N : TheoryTy _ tt
    N = ¬Ty (FollowLastTy (A *) c)

    Carrier : TheoryTy _ tt
    Carrier = N & (A *)

    nil-pf : εTy ⊢ N
    nil-pf =
      ⇒-intro (¬Nullable⊗r ¬Nullable-startsWith ∘⊢ &-swap ∘⊢ (id⊢ ,&p π₁))

    cons-pf : A ⊗ Carrier ⊢ N
    cons-pf = ⇒-intro body
      where
      D₀ : TheoryTy _ tt
      D₀ = A ⊗ Carrier

      W : TheoryTy _ tt
      W = (A ⊗ (A *)) ⊗ startsWith c

      S₁ S₂ : TheoryTy _ tt
      S₁ = (((A *) & εTy) ⊗ startsWith c)
      S₂ = (((A *) & char⁺) ⊗ startsWith c)

      -- the prefix before the `c` is empty, so `c` opens the whole `A *`
      emptyPrefix : D₀ & (S₁ & (A *)) ⊢ ⊥Ty
      emptyPrefix =
        π₂ ∘⊢ (id⊢ ,&p (∉First* hFA ∘⊢ ((⊗-unit-l ∘⊢ ⊗-map π₂ id⊢) ,&p id⊢)))

      -- ...the trailing `A *` is empty, so the `c` has nowhere to sit
      tailEmpty : (D₀ & W) & ((A *) & εTy) ⊢ ⊥Ty
      tailEmpty =
        char⁺-¬Nullable
        ∘⊢ ((¬Nullable→char⁺ (¬Nullable⊗r ¬Nullable-startsWith) ∘⊢ π₂ ∘⊢ π₁)
            ,& (π₂ ∘⊢ π₂))

      -- ...and the real case: both cuts are pinned and the tail's own
      -- refutation applies
      full : (D₀ & W) & ((A *) & char⁺) ⊢ ⊥Ty
      full =
        ⊗⊥-annihR
        ∘⊢ ⊗-map id⊢ (⇒-app ∘⊢ ((π₁ ∘⊢ π₁ ∘⊢ π₁) ,& (π₂ ,&p id⊢)))
        ∘⊢ ⊗&-distL (⊛∘⊢-r ⊛* (π₂ ∘⊢ π₁)) ⊛*
        ∘⊢ ((⊗-map π₁ id⊢
             ∘⊢ ⊗&-distL (⊛∘⊢-r ⊛* π₂)
                  (⊛-⊗ ⊛* (∉FollowLast→⊛ c hFLA disc))
             ∘⊢ (id⊢ ,&p ⊗-assoc)) ,&p nonmt*)

      -- the prefix is nonempty, so it is `A ⊗ A *` and the trailing `A *`
      -- decides which of the two above applies
      nonemptyPrefix : D₀ & (S₂ & (A *)) ⊢ ⊥Ty
      nonemptyPrefix =
        ⊕-elim& tailEmpty full
        ∘⊢ (id⊢ ,&p (stringSplit {A = A *}))
        ∘⊢ &-assoc
        ∘⊢ (id⊢ ,&p ((⊗-map nonmt* (id⊢ {A = startsWith c})) ,&p id⊢))

      splitPrefix : FollowLastTy (A *) c ⊢ (S₁ ⊕ S₂) & (A *)
      splitPrefix =
        (⊗⊕-distL ∘⊢ ⊗-map (stringSplit {A = A *}) (id⊢ {A = startsWith c}))
        ,&p id⊢

      body : D₀ & FollowLastTy (A *) c ⊢ ⊥Ty
      body =
        ⊕-elim&L (emptyPrefix ∘⊢ &-assoc⁻) (nonemptyPrefix ∘⊢ &-assoc⁻)
        ∘⊢ (&⊕-distR {A = D₀} {B = S₁} {C = S₂} ,&p id⊢)
        ∘⊢ &-assoc
        ∘⊢ (id⊢ ,&p splitPrefix)

    alg-nil : ⟦ starBranch A false ⟧TheoryTy (λ _ → Carrier) ⊢ Carrier
    alg-nil = (nil-pf ,& (NIL ∘⊢ liftTy)) ∘⊢ ⊗e-ε→ _

    alg-cons : ⟦ starBranch A true ⟧TheoryTy (λ _ → Carrier) ⊢ Carrier
    alg-cons =
      (cons-pf ,& (CONS ∘⊢ ⊗-map id⊢ π₂))
      ∘⊢ ⊗-map lowerTy lowerTy ∘⊢ ⟦⊗e⟧ _ _

  ∉FollowLast-* : c ∉FollowLast (A *)
  ∉FollowLast-* =
    ⇒-app
    ∘⊢ ((π₁ ∘⊢ π₂) ,& (id⊢ ,&p π₂))
    ∘⊢ (id⊢ ,&p fold*r alg-nil alg-cons)
