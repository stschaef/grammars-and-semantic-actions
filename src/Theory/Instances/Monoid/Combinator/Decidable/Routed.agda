{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Predictive choice indexed by the alternatives (production tags), not the cover's cells:
   no `⊥Set↑` pads, the cover reached only through `routeIn`, empty cells `nothing`.
   Known gap: the nullable case cannot be repaired — `E' ::= ε | '+' E` before another `E'`
   is genuinely ambiguous, so no route exists; prediction there needs the continuation-passed
   grammar.  Until then a nullable branch is *tried* by `_<|>_`, which is always sound. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Decidable.Routed
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Theory.Instances.Monoid.Combinator.Decidable.Base Alphabet _≟_ ℓ public
  hiding (Maybe ; just ; nothing)
