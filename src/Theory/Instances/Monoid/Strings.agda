{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- Free monoid via `List Alphabet`: `↓M tt` IS the list type, so
   `op ε· _` reduces to `[]` and `op _⊙_ ms` to `ms zero ++ ms (suc zero)`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Instances.Monoid.Strings
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Theory.Instances.Monoid.Strings.Base Alphabet isSetAlphabet public
open import Theory.Instances.Monoid.Strings.LinearProduct Alphabet isSetAlphabet public
open import Theory.Instances.Monoid.Strings.Distributivity Alphabet isSetAlphabet public
open import Theory.Instances.Monoid.Strings.Dependent Alphabet isSetAlphabet public
open import Theory.Instances.Monoid.Strings.HLevels Alphabet isSetAlphabet public
open import Theory.Instances.Monoid.Strings.Properties Alphabet isSetAlphabet public
open import Theory.Instances.Monoid.Strings.Terminal Alphabet isSetAlphabet public
