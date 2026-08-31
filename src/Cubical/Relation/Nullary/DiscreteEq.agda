module Cubical.Relation.Nullary.DiscreteEq where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary.Base using (Discrete ; yes ; no)
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)
open import Cubical.Data.Empty using (⊥)
import Cubical.Data.Sum as Sum
import Cubical.Data.Equality as Eq

private variable ℓY : Level

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
