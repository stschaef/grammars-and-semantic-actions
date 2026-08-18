-- Ordered choice, like a PEG
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

import Theory.Free.Base as FB
module Theory.Type.Decidable.Ordered
  {ℓ ℓ2 ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ2)
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Bool using (Bool ; true ; false)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Top.Base σeq V vs 𝒫
open import Theory.Type.Bottom.Base σeq V vs 𝒫
open import Theory.Type.Lift.Base σeq V vs 𝒫
open import Theory.Type.Sum.Base σeq V vs 𝒫
open import Theory.Type.Sum.Binary.Base σeq V vs 𝒫
open import Theory.Type.Product.Binary.Base σeq V vs 𝒫
open import Theory.Type.Function.Base σeq V vs 𝒫
open import Theory.Type.Cover.Base σeq V vs 𝒫
open import Theory.Type.Decidable.Base σeq V vs 𝒫

private variable ℓA ℓB ℓC : Level

_/_ : ∀ {s} → TheoryTy ℓA s → TheoryTy ℓB s → TheoryTy (ℓ-max ℓA ℓB) s
A / B = A ⊕ (¬Ty A & B)

infixr 17 _/_

module _ {s} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} where
  /-first : A ⊢ A / B
  /-first = inl

  /-second : ¬Ty A & B ⊢ A / B
  /-second = inr

module _ {s} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {C : TheoryTy ℓC s} where
  /-elim : A ⊢ C → ¬Ty A & B ⊢ C → A / B ⊢ C
  /-elim = ⊕-elim

/-branch : ∀ {s} (A : TheoryTy ℓA s) (B : TheoryTy ℓB s) → Bool
  → TheoryTy (ℓ-max ℓA ℓB) s
/-branch {ℓB = ℓB} A B true = LiftTheoryTy ℓB A
/-branch A B false = ¬Ty A & B

module _ {s} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} where
  /-disjoint : Disjoint (/-branch A B)
  /-disjoint true true neq = Empty.rec (neq Eq.refl)
  /-disjoint true false _ = ⇒-app ∘⊢ ((π₁ ∘⊢ π₂) ,& (lowerTy ∘⊢ π₁))
  /-disjoint false true _ = ⇒-app ∘⊢ ((π₁ ∘⊢ π₁) ,& (lowerTy ∘⊢ π₂))
  /-disjoint false false neq = Empty.rec (neq Eq.refl)

  /-total : Decidable A → Point B → Total (/-branch A B)
  /-total decA ptB =
    ⊕-elim (σ⊕ true ∘⊢ liftTy)
           (σ⊕ false ∘⊢ (id⊢ ,& (ptB ∘⊢ ⊤Ty-intro)))
    ∘⊢ decA

  /-cover : Decidable A → Point B → Cover Bool (/-branch A B)
  /-cover decA ptB .disjoint = /-disjoint
  /-cover decA ptB .total = /-total decA ptB

  -- deciding an ordered choice is deciding both branches
  dec/ : DecTy A & DecTy B ⊢ DecTy (A / B)
  dec/ = ⊕-elim& (dec-yes ∘⊢ /-first ∘⊢ π₂) no-A ∘⊢ &-swap
    where
    no-B : (¬Ty A & ¬Ty B) & (A / B) ⊢ ⊥Ty
    no-B = ⊕-elim& (⇒-app ∘⊢ ((π₁ ∘⊢ π₁) ,& π₂))
                   (⇒-app ∘⊢ ((π₂ ∘⊢ π₁) ,& (π₂ ∘⊢ π₂)))

    no-A : DecTy B & ¬Ty A ⊢ DecTy (A / B)
    no-A = ⊕-elim& (dec-yes ∘⊢ /-second) (dec-no ∘⊢ ⇒-intro no-B) ∘⊢ &-swap

  dec-/ : Decidable A → Decidable B → Decidable (A / B)
  dec-/ decA decB = dec/ ∘⊢ (decA ,& decB)
