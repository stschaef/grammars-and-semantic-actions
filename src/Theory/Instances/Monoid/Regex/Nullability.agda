-- Nullability as an index: a star can only be formed on a non-nullable body.
module Theory.Instances.Monoid.Regex.Nullability where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Empty as Empty

data Nullability : Type ℓ-zero where
  nullable notNullable : Nullability

ν≢ν̸ : nullable ≡ notNullable → Empty.⊥
ν≢ν̸ p = subst Discern p tt
  where
  Discern : Nullability → Type ℓ-zero
  Discern nullable = Unit
  Discern notNullable = Empty.⊥

-- Left-driven, so the indices reduce under a variable right argument.
_·ν_ : Nullability → Nullability → Nullability
notNullable ·ν _ = notNullable
nullable ·ν y = y

_+ν_ : Nullability → Nullability → Nullability
nullable +ν _ = nullable
notNullable +ν y = y
