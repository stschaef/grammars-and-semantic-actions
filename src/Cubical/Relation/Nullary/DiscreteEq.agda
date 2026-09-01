{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Cubical.Relation.Nullary.DiscreteEq where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary.Base using (Discrete ; yes ; no)
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)
open import Cubical.Data.Empty using (⊥)
import Cubical.Data.Sum as Sum
import Cubical.Data.Equality as Eq

open import Cubical.Data.Maybe using (Maybe ; just ; nothing)

private variable ℓY ℓZ ℓW : Level

DiscreteEq : Type ℓY → Type ℓY
DiscreteEq Y = (y y' : Y) → (y Eq.≡ y') Sum.⊎ ((y Eq.≡ y') → ⊥)

DiscreteEq→Discrete : {Y : Type ℓY} → DiscreteEq Y → Discrete Y
DiscreteEq→Discrete decY y y' = Sum.rec
  (λ p → yes (Eq.eqToPath p)) (λ ¬p → no λ p → ¬p (Eq.pathToEq p)) (decY y y')

DiscreteEq→isSet : {Y : Type ℓY} → DiscreteEq Y → isSet Y
DiscreteEq→isSet decY = Discrete→isSet (DiscreteEq→Discrete decY)

Discrete→DiscreteEq : {Y : Type ℓY} → Discrete Y → DiscreteEq Y
Discrete→DiscreteEq d y y' with d y y'
... | yes p = Sum.inl (Eq.pathToEq p)
... | no ¬p = Sum.inr (λ q → ¬p (Eq.eqToPath q))

-- Structural combinators; direct pattern matches so decisions built from
-- them still reduce in one step on canonical inputs.
discreteEqCong : {Y : Type ℓY} {Z : Type ℓZ} {y y' : Y} (f : Y → Z)
  → (f y Eq.≡ f y' → y Eq.≡ y')
  → (y Eq.≡ y') Sum.⊎ ((y Eq.≡ y') → ⊥)
  → (f y Eq.≡ f y') Sum.⊎ ((f y Eq.≡ f y') → ⊥)
discreteEqCong f inj (Sum.inl Eq.refl) = Sum.inl Eq.refl
discreteEqCong f inj (Sum.inr ne) = Sum.inr λ e → ne (inj e)

discreteEqCong2 : {Y : Type ℓY} {Z : Type ℓZ} {W : Type ℓW}
  {y y' : Y} {z z' : Z} (f : Y → Z → W)
  → (f y z Eq.≡ f y' z' → y Eq.≡ y')
  → (f y z Eq.≡ f y' z' → z Eq.≡ z')
  → (y Eq.≡ y') Sum.⊎ ((y Eq.≡ y') → ⊥)
  → (z Eq.≡ z') Sum.⊎ ((z Eq.≡ z') → ⊥)
  → (f y z Eq.≡ f y' z') Sum.⊎ ((f y z Eq.≡ f y' z') → ⊥)
discreteEqCong2 f inj1 inj2 (Sum.inl Eq.refl) (Sum.inl Eq.refl) = Sum.inl Eq.refl
discreteEqCong2 f inj1 inj2 (Sum.inr ne) _ = Sum.inr λ e → ne (inj1 e)
discreteEqCong2 f inj1 inj2 _ (Sum.inr ne) = Sum.inr λ e → ne (inj2 e)

discreteEqMaybe : {Y : Type ℓY} → DiscreteEq Y → DiscreteEq (Maybe Y)
discreteEqMaybe d nothing nothing = Sum.inl Eq.refl
discreteEqMaybe d nothing (just _) = Sum.inr λ ()
discreteEqMaybe d (just _) nothing = Sum.inr λ ()
discreteEqMaybe d (just x) (just y) =
  discreteEqCong just (λ where Eq.refl → Eq.refl) (d x y)
