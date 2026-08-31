{- Decidable equality valued in `Cubical.Data.Equality`'s strict `_≡_`, and
   the `isSet` it yields.

   `DiscreteEq` was declared in `Theory/Type/Decidable/Route`, which has
   nothing to do with routing, and the bridge to `isSet` was written out
   five times: `Combinator/Core` had it as a definition and
   `Monoid/Types`, `Monoid/Unicode/Base` and `Decidable/Productions` each
   re-inlined `Discrete→isSet ∘ Sum.rec`, two of them because they are
   imported *by* `Combinator/Core` and so could not use its copy.

   Neither notion mentions a theory, a signature or a presentation, so
   neither belongs in a module parameterised by one -- hence this
   parameter-free home, where every one of those callers can reach it. -}
module Cubical.Relation.Nullary.DiscreteEq where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary.Base using (Discrete ; yes ; no)
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)
open import Cubical.Data.Empty using (⊥)
import Cubical.Data.Sum as Sum
import Cubical.Data.Equality as Eq

private variable ℓY : Level

-- Deciding an index in `Eq`, so that matching refines.
DiscreteEq : Type ℓY → Type ℓY
DiscreteEq Y = (y y' : Y) → (y Eq.≡ y') Sum.⊎ ((y Eq.≡ y') → ⊥)

DiscreteEq→Discrete : {Y : Type ℓY} → DiscreteEq Y → Discrete Y
DiscreteEq→Discrete decY y y' = Sum.rec
  (λ p → yes (Eq.eqToPath p)) (λ ¬p → no λ p → ¬p (Eq.pathToEq p)) (decY y y')

-- A definition rather than an inlined `Discrete→isSet` so that a grammar
-- may name the *same* proof the `Choice` module will use: `⊕ᴰSet` is
-- definitional in its proof.
DiscreteEq→isSet : {Y : Type ℓY} → DiscreteEq Y → isSet Y
DiscreteEq→isSet decY = Discrete→isSet (DiscreteEq→Discrete decY)

-- ...and back, so that a `Discrete` obtained from any of the usual sources
-- (an injection, `discreteℕ`, `discreteFin`) can serve as a `DiscreteEq`
-- without a hand-written table.
Discrete→DiscreteEq : {Y : Type ℓY} → Discrete Y → DiscreteEq Y
Discrete→DiscreteEq d y y' with d y y'
... | yes p = Sum.inl (Eq.pathToEq p)
... | no ¬p = Sum.inr (λ q → ¬p (Eq.eqToPath q))
