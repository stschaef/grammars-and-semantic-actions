{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The readout: an occurrence, folded to the position it sits at.

   Convention 8, and the case that makes it worth having.  `posAction`
   counts the `inr`s in a derivation of `Occurs y`, which is convention 7's
   observation at its smallest -- a `Bool` would say that `y` is in the
   bag, a chain of "not here" steps ending in a hit says WHERE, and
   counting the steps is the index.  The readout READS the derivation; it
   does not search the list again.

   The three front ends are the same three-term composition every other
   client spells, and here they genuinely differ, because `Occurs` is not a
   proposition.  `Dec` collapses the alternatives to a decision and
   `observe` reads the one derivation it kept; `Maybe` commits to the
   leftmost, so `firstAt` is the first occurrence; `ND` keeps them all, and
   `observeND` crosses the boundary once per derivation, so `everyAt` is
   the list of every position.

   And that list is where the quotient reappears.  `everyAt` is not a
   function of the bag -- the positions are positions in a REPRESENTATIVE,
   and `Chosen/Quotient`'s `toBag-swap` moves them.  Its LENGTH is a
   function of the bag, because multiplicity is a fold.  A readout is
   permutation-invariant exactly as far as its answer is. -}
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

-- Counting the steps that missed.
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
