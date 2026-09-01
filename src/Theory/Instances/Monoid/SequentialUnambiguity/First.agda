{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
-- First sets, as refutations: `c ∉First A` says no `A`-word begins with `c`.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.SequentialUnambiguity.First
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List as L using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt ; tt*)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Precise Alphabet isSetAlphabet using (flat)
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet
  using (_* ; unroll* ; starBranch ; fold*r) public
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (two-η ; &⊕-distR ; ⊗⊕ᴰ-distL)
open import Theory.Instances.Monoid.Convolution Alphabet isSetAlphabet
  using (⟦⊗e⟧ ; ⊗e-ε→)
open import Theory.Instances.Monoid.SequentialUnambiguity.Nullable
  Alphabet isSetAlphabet public
open import Theory.Type.Unambiguity.Disjoint MonEqns Alphabet (λ _ → tt)
  listPresentation using (disjoint) public

private variable ℓA ℓB ℓC ℓD : Level

startsWith : Alphabet → TheoryTy ℓM tt
startsWith c = literal c ⊗ ⊤Ty

startsWith→char⁺ : (c : Alphabet) → startsWith c ⊢ char⁺
startsWith→char⁺ c = ⊗-map (σ⊕ c) read

¬Nullable-startsWith : {c : Alphabet} → ¬Nullable (startsWith c)
¬Nullable-startsWith {c} = ¬Nullable-map (startsWith→char⁺ c) char⁺-¬Nullable

FirstTy : TheoryTy ℓA tt → Alphabet → TheoryTy _ tt
FirstTy A c = startsWith c & A

_∉First_ : Alphabet → TheoryTy ℓA tt → Type _
c ∉First A = FirstTy A c ⊢ ⊥Ty

∉First∘⊢ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {c : Alphabet}
  → (f : B ⊢ A) → c ∉First A → c ∉First B
∉First∘⊢ f h = h ∘⊢ (id⊢ ,&p f)

∉First-⊕ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {c : Alphabet}
  → c ∉First A → c ∉First B → c ∉First (A ⊕ B)
∉First-⊕ hA hB = ⊕-elim& hA hB

∉First-⊕ᴰ : {Y : Type ℓB} {A : Y → TheoryTy ℓA tt} {c : Alphabet}
  → ((y : Y) → c ∉First (A y)) → c ∉First (⊕[ y ∈ Y ] A y)
∉First-⊕ᴰ h m (sw , (y , a)) = h y m (sw , a)

∉First-⊥ : {c : Alphabet} → c ∉First (⊥Ty {s = tt})
∉First-⊥ = ⊥Ty-elim ∘⊢ π₂

∉First-ε : {c : Alphabet} → c ∉First εTy
∉First-ε = ¬Nullable-startsWith

-- matching the left factor's word makes the head letter available
private
  split-go : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} (c : Alphabet)
    → ¬Nullable A → (m : String) (x y : String)
    → op _⊙_ (two x y) Eq.≡ m → A x → B y → startsWith c m
    → ((startsWith c & A) ⊗ B) m
  split-go c nu m [] y e a b sw = Empty.rec (lower (nu [] (a , εTy-pt)))
  split-go {A = A} {B = B} c nu m (d ∷ x) y e a b sw =
    two (d ∷ x) y , e , ((headed , a) , (b , tt*))
    where
    d≡c : d ≡ c
    d≡c = L.cons-inj₁
      (Eq.eqToPath e
      ∙ sym (flat c (sw .fst zero) (sw .fst (suc zero)) m
              (sw .snd .snd .fst) (sw .snd .fst)))

    headed : startsWith c (d ∷ x)
    headed =
      two (c ∷ []) x
      , Eq.pathToEq (cong (_∷ x) (sym d≡c))
      , (Eq.refl , (tt , tt*))

first⊗-split : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} (c : Alphabet)
  → ¬Nullable A → startsWith c & (A ⊗ B) ⊢ (startsWith c & A) ⊗ B
first⊗-split {A = A} {B = B} c nu m (sw , (ms , e , (a , (b , _)))) =
  subst (λ ns → op _⊙_ ns Eq.≡ m → A (ns zero) → B (ns (suc zero))
               → startsWith c m → ((startsWith c & A) ⊗ B) m)
    (two-η ms) (split-go c nu m (ms zero) (ms (suc zero))) e a b sw

∉First⊗l : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {c : Alphabet}
  → ¬Nullable A → c ∉First A → c ∉First (A ⊗ B)
∉First⊗l {c = c} nu h = ⊗⊥-annihL ∘⊢ ⊗-map h id⊢ ∘⊢ first⊗-split c nu

∉First⊗ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {c : Alphabet}
  → c ∉First A → c ∉First B → c ∉First (A ⊗ B)
∉First⊗ {A = A} {B = B} {c = c} hA hB =
  ⊕-elim
    (hB ∘⊢ (id⊢ ,&p (⊗-unit-l ∘⊢ ⊗-map π₂ id⊢)))
    (∉First⊗l ¬Nullable-&char⁺ (∉First∘⊢ π₁ hA))
  ∘⊢ &⊕-distR
  ∘⊢ (π₁ ,& (⊗⊕-distL ∘⊢ ⊗-map stringSplit id⊢ ∘⊢ π₂))

_#_ : TheoryTy ℓA tt → TheoryTy ℓB tt → Type _
A # B = (c : Alphabet) → (c ∉First A) Sum.⊎ (c ∉First B)

sym# : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} → A # B → B # A
sym# sep c = Sum.rec Sum.inr Sum.inl (sep c)

#∘⊢ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → A ⊢ B → B # C → A # C
#∘⊢ f sep c = Sum.map (∉First∘⊢ f) (λ x → x) (sep c)

#∘⊢2 : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  {C : TheoryTy ℓC tt} {D : TheoryTy ℓD tt}
  → A ⊢ B → C ⊢ D → B # D → A # C
#∘⊢2 f g sep c = Sum.map (∉First∘⊢ f) (∉First∘⊢ g) (sep c)

#⊗l : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → ¬Nullable A → A # B → (A ⊗ C) # B
#⊗l nu sep c = Sum.map (∉First⊗l nu) (λ x → x) (sep c)

char⁺→⊕startsWith : char⁺ ⊢ ⊕[ c ∈ Alphabet ] startsWith c
char⁺→⊕startsWith =
  map⊕ᴰ (λ c → ⊗-map id⊢ ⊤Ty-intro) ∘⊢ ⊗⊕ᴰ-distL

#→disjoint : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → A # B → (¬Nullable A) Sum.⊎ (¬Nullable B) → disjoint A B
#→disjoint {A = A} {B = B} sep nu =
  ⊕-elim
    (Sum.rec (λ nuA → nuA ∘⊢ ((π₁ ∘⊢ π₁) ,& π₂))
             (λ nuB → nuB ∘⊢ ((π₂ ∘⊢ π₁) ,& π₂)) nu)
    (⊕ᴰ-elim (λ c → Sum.rec
        (λ hA → hA ∘⊢ (π₂ ,& (π₁ ∘⊢ π₁)))
        (λ hB → hB ∘⊢ (π₂ ,& (π₂ ∘⊢ π₁)))
        (sep c))
      ∘⊢ &⊕ᴰ-distR
      ∘⊢ (π₁ ,& (char⁺→⊕startsWith ∘⊢ π₂)))
  ∘⊢ stringSplit

-- with `A` non-nullable, one unrolling is enough
∉First*-notnull : {A : TheoryTy ℓA tt} {c : Alphabet}
  → ¬Nullable A → c ∉First A → c ∉First (A *)
∉First*-notnull nu h =
  ⊕-elim& (∉First⊗l nu h) (∉First∘⊢ lowerTy ∉First-ε)
  ∘⊢ (id⊢ ,&p unroll*)

-- without non-nullability the unrolling can loop, so build the refutation
-- by a fold
∉First* : {A : TheoryTy ℓA tt} {c : Alphabet} → c ∉First A → c ∉First (A *)
∉First* {A = A} {c = c} h =
  ⇒-app ∘⊢ &-swap ∘⊢ (id⊢ ,&p fold*r nil-branch cons-branch)
  where
  N : TheoryTy _ tt
  N = ¬Ty (startsWith c)

  nil-branch : ⟦ starBranch A false ⟧TheoryTy (λ _ → N) ⊢ N
  nil-branch = ⇒-intro (¬Nullable-startsWith ∘⊢ &-swap) ∘⊢ ⊗e-ε→ _

  cons-branch : ⟦ starBranch A true ⟧TheoryTy (λ _ → N) ⊢ N
  cons-branch =
    ⇒-intro
      (⊕-elim&
        (⇒-app ∘⊢ ((⊗-unit-l ∘⊢ ⊗-map π₂ id⊢ ∘⊢ π₂) ,& π₁))
        (∉First⊗l ¬Nullable-&char⁺ (∉First∘⊢ π₁ h))
      ∘⊢ &-swap
      ∘⊢ ((⊗⊕-distL ∘⊢ ⊗-map stringSplit id⊢) ,&p id⊢))
    ∘⊢ ⊗-map lowerTy lowerTy ∘⊢ ⟦⊗e⟧ _ _
