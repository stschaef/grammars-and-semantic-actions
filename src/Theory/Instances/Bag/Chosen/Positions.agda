{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Occurrences folded to the position they sit at.  `everyAt` is not a
   function of the bag -- positions live in a REPRESENTATIVE and `toBag-swap`
   moves them -- but its LENGTH is, because multiplicity is a fold. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Bag.Chosen.Positions
  (El : Type ℓ-zero) (isSetEl : isSet El) where

open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Unit using (tt)
open import Cubical.Relation.Nullary.Base using (Discrete)
import Cubical.Data.Sum as Sum

open import Theory.Instances.Bag.Chosen.Occurs El isSetEl public
open import Theory.Type.SemanticAction.Base CEqns ⊥ noVar cPresentation

import Theory.Combinator.Answer.Decidable CEqns ⊥ noVar cPresentation as D
import Theory.Combinator.Answer.Incomplete CEqns ⊥ noVar cPresentation as MB
import Theory.Combinator.Answer.NonDet CEqns ⊥ noVar cPresentation as NDm

posAction : (y : El) → SemanticAction (Occurs y) ℕ
posAction y (x ∷ l) (Sum.inl p) = zero , tt
posAction y (x ∷ l) (Sum.inr o) = suc (posAction y l o .fst) , tt

module _ (discEl : Discrete El) where

  private
    module CD = Check discEl D.DecAnswer
    module CM = Check discEl MB.MaybeAnswer
    module CN = Check discEl NDm.NDAnswer

  -- `Dec`: a position if there is one, and a refutation otherwise.
  positionOf : (y : El) → List El → Maybe ℕ
  positionOf y = observe (CD.contains y) (semact-dec (posAction y))

  -- `Maybe`: the same, by committing left rather than by deciding.
  firstAt : (y : El) → List El → Maybe ℕ
  firstAt y = observe (CM.contains y) (semact-Maybe (posAction y))

  -- `ND`: every occurrence, read out once per derivation.
  everyAt : (y : El) → List El → List ℕ
  everyAt y l = NDm.observeND (CN.contains y) (posAction y) l
