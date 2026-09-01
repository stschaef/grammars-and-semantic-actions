{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- Routing a coproduct through a cover.
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

import Theory.Free.Base as FB
module Theory.Type.Decidable.Route
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
import Cubical.Data.Sum as Sum
import Cubical.Data.Equality as Eq

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Bottom.Base σeq V vs 𝒫
open import Theory.Type.Top.Base σeq V vs 𝒫
open import Theory.Type.Function.Base σeq V vs 𝒫
open import Theory.Type.Product.Base σeq V vs 𝒫
open import Theory.Type.Product.Binary.Base σeq V vs 𝒫
open import Theory.Type.Sum.Base σeq V vs 𝒫
open import Theory.Type.Distributivity σeq V vs 𝒫 using (&⊕ᴰ-distR)
open import Theory.Type.Sum.Binary.Base σeq V vs 𝒫
open import Theory.Type.Cover.Base σeq V vs 𝒫
open import Theory.Type.Decidable.Base σeq V vs 𝒫

private variable ℓA ℓB ℓY : Level

open import Cubical.Relation.Nullary.DiscreteEq public
  using (DiscreteEq ; DiscreteEq→Discrete ; DiscreteEq→isSet)

module _ {s} {Y : Type ℓY} (Φ : Y → TheoryTy ℓA s) where

  record Route (ℓB : Level)
    : Type (ℓ-max ℓY (ℓ-max ℓM (ℓ-max ℓA (ℓ-suc ℓB)))) where
    field
      B    : Maybe Y → TheoryTy ℓB s
      cov  : Cover (Maybe Y) B
      into : (y : Y) → Φ y ⊢ B (just y)

  open Route

  routeIn : Route ℓB → DiscreteEq Y
    → (&[ y ∈ Y ] DecTy (Φ y)) ⊢ DecTy (⊕[ y ∈ Y ] Φ y)
  routeIn R decY =
    ⊕ᴰ-elim step ∘⊢ &⊕ᴰ-distR ∘⊢ (id⊢ ,& (R .cov .total ∘⊢ ⊤Ty-intro))
    where
    Ds : TheoryTy _ s
    Ds = &[ y ∈ Y ] DecTy (Φ y)

    elsewhere : (v : Maybe Y) (y : Y) → (v Eq.≡ just y → ⊥)
      → R .B v ⊢ ¬Ty (Φ y)
    elsewhere v y ne =
      ⇒-intro (R .cov .disjoint v (just y) ne ∘⊢ (id⊢ ,&p R .into y))

    step : (v : Maybe Y) → Ds & R .B v ⊢ DecTy (⊕[ y ∈ Y ] Φ y)
    step nothing =
      dec-no ∘⊢ ¬⊕ᴰ ∘⊢ &ᴰ-intro λ y →
        elsewhere nothing y (λ ()) ∘⊢ π₂
    step (just y₀) =
      ⊕-elim& (dec-yes ∘⊢ σ⊕ y₀ ∘⊢ π₂)
              (dec-no ∘⊢ ¬⊕ᴰ ∘⊢ &ᴰ-intro kill)
      ∘⊢ (id⊢ ,& (π y₀ ∘⊢ π₁))
      where
      kill : (y : Y) → (Ds & R .B (just y₀)) & ¬Ty (Φ y₀) ⊢ ¬Ty (Φ y)
      kill y = same (decY y₀ y)
        where
        same : (y₀ Eq.≡ y) Sum.⊎ ((y₀ Eq.≡ y) → ⊥)
          → (Ds & R .B (just y₀)) & ¬Ty (Φ y₀) ⊢ ¬Ty (Φ y)
        same (Sum.inl Eq.refl) = π₂
        same (Sum.inr ne) =
          elsewhere (just y₀) y (λ where Eq.refl → ne Eq.refl)
          ∘⊢ π₂ ∘⊢ π₁

  routeDec : Route ℓB → DiscreteEq Y
    → ((y : Y) → Decidable (Φ y))
    → Decidable (⊕[ y ∈ Y ] Φ y)
  routeDec R decY decΦ = routeIn R decY ∘⊢ &ᴰ-intro decΦ
