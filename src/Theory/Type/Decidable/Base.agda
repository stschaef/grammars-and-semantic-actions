-- Decidability as a theory type: `DecTy A = A ⊕ ¬Ty A`.
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

import Theory.Free.Base as FB
module Theory.Type.Decidable.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
import Cubical.Data.Sum as Sum
import Cubical.Data.Equality as Eq

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Bottom.Base σeq V vs 𝒫
open import Theory.Type.Top.Base σeq V vs 𝒫
open import Theory.Type.Function.Base σeq V vs 𝒫
open import Theory.Type.Product.Base σeq V vs 𝒫
open import Theory.Type.Product.Binary.Base σeq V vs 𝒫
open import Theory.Type.Sum.Base σeq V vs 𝒫
open import Theory.Type.Sum.Binary.Base σeq V vs 𝒫
open import Theory.Type.Lift.Base σeq V vs 𝒫
open import Theory.Type.Operation.Base σeq V vs 𝒫
open import Theory.Type.Cover.Base σeq V vs 𝒫

open import Theory.Type.Negation.Base σeq V vs 𝒫 public

private variable ℓA ℓB : Level

DecTy : ∀ {s} → TheoryTy ℓA s → TheoryTy ℓA s
DecTy A = A ⊕ ¬Ty A

Decidable : ∀ {s} → TheoryTy ℓA s → Type _
Decidable A = ⊤Ty ⊢ DecTy A

DecAt : ∀ {s} → TheoryTy ℓA s → ↓M s → Type ℓA
DecAt A m = DecTy A m

at : ∀ {s} {A : TheoryTy ℓA s} → Decidable A → ∀ m → DecAt A m
at decA m = decA m tt

dec-yes : ∀ {s} {A : TheoryTy ℓA s} → A ⊢ DecTy A
dec-yes = inl

dec-no : ∀ {s} {A : TheoryTy ℓA s} → ¬Ty A ⊢ DecTy A
dec-no = inr

¬Ty-map : ∀ {s} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  → B ⊢ A → ¬Ty A ⊢ ¬Ty B
¬Ty-map f m na b = na (f m b)

module _ {s} {A : TheoryTy ℓA s} {m : ↓M s} where
  isNo : DecTy A m → Bool
  isNo (Sum.inl _) = false
  isNo (Sum.inr _) = true

  theNo : (d : DecTy A m) → isNo d Eq.≡ true → ¬Ty A m
  theNo (Sum.inr na) _ = na

  isYes : DecTy A m → Bool
  isYes (Sum.inl _) = true
  isYes (Sum.inr _) = false

  theYes : (d : DecTy A m) → isYes d Eq.≡ true → A m
  theYes (Sum.inl a) _ = a

isProp¬Ty : ∀ {s} (A : TheoryTy ℓA s) {m : ↓M s} → isProp (¬Ty A m)
isProp¬Ty A p q = funExt λ x → Empty.rec* (p x)

¬⊕ᴰ : ∀ {ℓY s} {Y : Type ℓY} {A : Y → TheoryTy ℓA s}
  → (&[ y ∈ Y ] ¬Ty (A y)) ⊢ ¬Ty (⊕[ y ∈ Y ] A y)
¬⊕ᴰ m f (y , a) = f y a

¬-⊕ : ∀ {s} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  → ¬Ty A & ¬Ty B ⊢ ¬Ty (A ⊕ B)
¬-⊕ = ⇒-intro (⊕-elim& (⇒-app ∘⊢ ((π₁ ∘⊢ π₁) ,& π₂))
                       (⇒-app ∘⊢ ((π₂ ∘⊢ π₁) ,& π₂)))

dec-⊕& : ∀ {s} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  → DecTy A & DecTy B ⊢ DecTy (A ⊕ B)
dec-⊕& =
  ⊕-elim& (dec-yes ∘⊢ inl ∘⊢ π₂)
          (⊕-elim& (dec-yes ∘⊢ inr ∘⊢ π₂) (dec-no ∘⊢ ¬-⊕) ∘⊢ &-swap)
  ∘⊢ &-swap

dec-map : ∀ {s} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  → A ⊢ B → ¬Ty A ⊢ ¬Ty B → DecTy A ⊢ DecTy B
dec-map f nf = ⊕-elim (dec-yes ∘⊢ f) (dec-no ∘⊢ nf)

-- Pointwise decisions assemble into a decider; refutations land in `⊥Ty`
-- because `¬Ty` is the pointwise function type.
dec-fromDec : ∀ {s} {A : TheoryTy ℓA s}
  → ((m : ↓M s) → Dec (A m)) → Decidable A
dec-fromDec d m _ with d m
... | yes a = Sum.inl a
... | no ¬a = Sum.inr λ a → Empty.rec (¬a a)

dec-retract : ∀ {s} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  → A ⊢ B → B ⊢ A → Decidable A → Decidable B
dec-retract f g d = dec-map f (¬Ty-map g) ∘⊢ d

dec-retract-id : ∀ {s} {A : TheoryTy ℓA s} (d : Decidable A)
  → dec-retract id⊢ id⊢ d ≡ d
dec-retract-id {A = A} d = funExt λ m → funExt λ u → id-at-answer m (d m u)
  where
  id-at-answer : (m : ↓M _) (z : DecAt A m)
     → dec-map {A = A} {B = A} id⊢ (¬Ty-map id⊢) m z ≡ z
  id-at-answer m (Sum.inl a) = refl
  id-at-answer m (Sum.inr na) = refl

dec-retract-∘ : ∀ {ℓC s} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  {C : TheoryTy ℓC s}
  (f : A ⊢ B) (g : B ⊢ A) (f' : B ⊢ C) (g' : C ⊢ B) (d : Decidable A)
  → dec-retract f' g' (dec-retract f g d) ≡ dec-retract (f' ∘⊢ f) (g ∘⊢ g') d
dec-retract-∘ {A = A} f g f' g' d = funExt λ m → funExt λ u → ∘-at-answer m (d m u)
  where
  ∘-at-answer : (m : ↓M _) (z : DecAt A m)
     → dec-map f' (¬Ty-map g') m (dec-map f (¬Ty-map g) m z)
       ≡ dec-map (f' ∘⊢ f) (¬Ty-map (g ∘⊢ g')) m z
  ∘-at-answer m (Sum.inl a) = refl
  ∘-at-answer m (Sum.inr na) = refl

dec⊥Ty : ∀ {s} → Decidable (⊥Ty {s = s})
dec⊥Ty m _ = Sum.inr (λ ())

dec⊤Ty : ∀ {s} → Decidable (⊤Ty {s = s})
dec⊤Ty m _ = Sum.inl tt

dec⊕ : ∀ {s} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  → Decidable A → Decidable B → Decidable (A ⊕ B)
dec⊕ decA decB = dec-⊕& ∘⊢ (decA ,& decB)

dec& : ∀ {s} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  → Decidable A → Decidable B → Decidable (A & B)
dec& decA decB m _ with decA m tt
... | Sum.inr notA = Sum.inr λ ab → notA (ab .fst)
... | Sum.inl a with decB m tt
... | Sum.inr notB = Sum.inr λ ab → notB (ab .snd)
... | Sum.inl b = Sum.inl (a , b)

decLiftTheoryTy : ∀ {s} {A : TheoryTy ℓA s}
  → Decidable A → Decidable (LiftTheoryTy ℓB A)
decLiftTheoryTy decA m _ with decA m tt
... | Sum.inl a = Sum.inl (lift a)
... | Sum.inr notA = Sum.inr λ z → notA (z .lower)


DecCover : ∀ {s} → TheoryTy ℓA s → Bool → TheoryTy ℓA s
DecCover A true = A
DecCover A false = ¬Ty A

decisionCover : ∀ {s} {A : TheoryTy ℓA s}
  → Decidable A → Cover Bool (DecCover A)
decisionCover dec .disjoint true true neq m (a , notA) = lift (neq Eq.refl)
decisionCover dec .disjoint true false neq m (a , notA) = notA a
decisionCover dec .disjoint false true neq m (notA , a) = notA a
decisionCover dec .disjoint false false neq m (notA , a) = lift (neq Eq.refl)
decisionCover dec .total =
  ⊕-elim (σ⊕ true) (σ⊕ false) ∘⊢ dec

coverDecidable : ∀ {s} {A : TheoryTy ℓA s}
  → Cover Bool (DecCover A) → Decidable A
coverDecidable c = cover-elim c λ where
  true → dec-yes
  false → dec-no

dec-cover : ∀ {ℓY s} {Y : Type ℓY} {A : Y → TheoryTy ℓA s}
  → ((y y' : Y) → (y Eq.≡ y') Sum.⊎ ((y Eq.≡ y') → ⊥))
  → Cover Y A → (y : Y) → Decidable (A y)
dec-cover {A = A} decY c y = cover-elim c step
  where
  step : ∀ y' → A y' ⊢ DecTy (A y)
  step y' = by-index-eq (decY y' y)
    where
    by-index-eq : (y' Eq.≡ y) Sum.⊎ ((y' Eq.≡ y) → ⊥) → A y' ⊢ DecTy (A y)
    by-index-eq (Sum.inl Eq.refl) = dec-yes
    by-index-eq (Sum.inr ne) = dec-no ∘⊢ ⇒-intro (c .disjoint y' y ne)
