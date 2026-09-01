{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `Combinator/Syntax` at `MaybeAnswer`; this module only chooses the answer. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Combinator.Incomplete.Star
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Theory.Instances.Monoid.Combinator.Incomplete.Base Alphabet _≟_ ℓ public
open import Theory.Instances.Monoid.Combinator.Syntax
  Alphabet _≟_ MaybeAnswer public
