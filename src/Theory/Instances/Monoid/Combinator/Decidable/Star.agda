{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `Combinator/Syntax` at `DecAnswer`.  `many`, `some`, `option`,
   `between`, `sepBy` and the regex compiler are written once and live
   there; this module only chooses the answer. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Combinator.Decidable.Star
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Theory.Instances.Monoid.Combinator.Decidable.Base Alphabet _≟_ ℓ public
open import Theory.Instances.Monoid.Combinator.Syntax
  Alphabet _≟_ DecAnswer public
