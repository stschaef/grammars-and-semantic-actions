{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Equality as Eq
open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open SortedSig
open SortedEqns
module Theory.Instances.Bags.Sorted.HLevels
  (El : Type ℓ-zero) (isSetEl : isSet El) (le : El → El → Bool) where

open import Cubical.Data.Unit using (Unit ; tt ; tt*)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Bags.Base El
open import Theory.Instances.Bags.Order El le
open import Theory.Instances.Bags.Sorted.Base El le
open import Theory.Instances.Bags.HLevels El isSetEl using (isSet⌈⌉ ; isSetεB)
open import Theory.Type.HLevels BagEqns El (λ _ → tt) closingPresentation
open import Theory.Type.Inductive.HLevels BagEqns El (λ _ → tt) closingPresentation

isSetValuedSortedCode : isSetValued {X = Unit} {xs = λ _ → tt} SortedCode
isSetValuedSortedCode =
  lift isSetBool , λ where
    false → lift isSetεB
    true →
      lift isSetEl , λ x → two
        (lift (isSet⌈⌉ ⌈gen x ⌉))
        (lift tt* , lift (isSetLiftTheoryTy (isSetAbove x)))

isSetSorted : isSetTheoryTy Sorted
isSetSorted = isSetμ (λ _ → SortedCode) (λ _ → isSetValuedSortedCode) tt
