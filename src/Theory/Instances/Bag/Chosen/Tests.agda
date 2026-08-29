{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Two judgments, three answers, and one permutation.  The tests are
   `refl`, so the typechecker runs the checker, the guarded fixpoint and
   every backend on concrete bags.

   The permutation block is the one that matters.  `[ 1 , 2 ]` and
   `[ 2 , 1 ]` are the SAME BAG -- `Chosen/Quotient`'s `toBag-swap` proves
   it -- and the two clients disagree about whether that sentence means
   anything.
   `Occurs` gives them the same answer at all three backends, and at `ND`
   the answer is the multiplicity, which is a bag invariant.  `Sorted`
   gives them different answers, so it is not a predicate on bags at all.

   `ND` counting 1 for a sorted bag is a typing fact: `Sorted` is a
   proposition.  `ND` counting 2 for `2` in `[ 1 , 2 , 2 , 5 ]` is the other
   kind of fact: `Occurs` is proof-relevant on purpose, and the enumerating
   answer is the only one that can see it.

   The last block runs `Chosen/Positions`, the readout, and makes the same
   point once more at the level of values: the list of positions moves
   under the permutation and its length does not. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Bag.Chosen.Tests where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Maybe using (Maybe ; nothing ; just)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ ; discreteℕ)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Sum as Sum

-- The order, as a boolean test, so that everything reduces.
leℕ : ℕ → ℕ → Bool
leℕ zero _ = true
leℕ (suc m) zero = false
leℕ (suc m) (suc n) = leℕ m n

open import Theory.Instances.Bag.Chosen.Guard ℕ isSetℕ

import Theory.Instances.Bag.Chosen.Sorted ℕ isSetℕ leℕ as S
import Theory.Instances.Bag.Chosen.Occurs ℕ isSetℕ as O

import Theory.Combinator.Answer.Decidable CEqns ⊥ noVar cPresentation as D
import Theory.Combinator.Answer.Incomplete CEqns ⊥ noVar cPresentation as MB
import Theory.Combinator.Answer.NonDet CEqns ⊥ noVar cPresentation as NDm

module SD = S.Check D.DecAnswer
module SM = S.Check MB.MaybeAnswer
module SN = S.Check NDm.NDAnswer

module OD = O.Check discreteℕ D.DecAnswer
module OM = O.Check discreteℕ MB.MaybeAnswer
module ON = O.Check discreteℕ NDm.NDAnswer

-- the same two grammars, read three ways
sortedD sortedM : List ℕ → Bool
sortedD l = Sum.rec (λ _ → true) (λ _ → false) (SD.inOrder nothing l tt)
sortedM l = Sum.rec (λ _ → true) (λ _ → false) (SM.inOrder nothing l tt)

sortedN : List ℕ → ℕ
sortedN l = length (NDm.ndToList l (SN.inOrder nothing l tt))

occursD occursM : ℕ → List ℕ → Bool
occursD y l = Sum.rec (λ _ → true) (λ _ → false) (OD.contains y l tt)
occursM y l = Sum.rec (λ _ → true) (λ _ → false) (OM.contains y l tt)

multiplicity : ℕ → List ℕ → ℕ
multiplicity y l = length (NDm.ndToList l (ON.contains y l tt))


-- Bags, spelled as their chosen representatives.
nowt asc dup desc plateau : List ℕ
nowt = []
asc = 1 ∷ 2 ∷ 5 ∷ []
dup = 1 ∷ 2 ∷ 2 ∷ 5 ∷ []
desc = 5 ∷ 2 ∷ 1 ∷ []
plateau = 3 ∷ 3 ∷ []


-- SORTEDNESS, at `Dec`.
dec-nowt : sortedD nowt ≡ true
dec-nowt = refl

dec-asc : sortedD asc ≡ true
dec-asc = refl

dec-dup : sortedD dup ≡ true
dec-dup = refl

dec-plateau : sortedD plateau ≡ true
dec-plateau = refl

dec-desc : sortedD desc ≡ false
dec-desc = refl

-- `Maybe` agrees; it has nothing to commit to, since there is one rule per
-- head.
may-asc : sortedM asc ≡ true
may-asc = refl

may-desc : sortedM desc ≡ false
may-desc = refl

-- ...and `ND` finds exactly one derivation, since `Sorted` is a
-- proposition.
nd-asc : sortedN asc ≡ 1
nd-asc = refl

nd-desc : sortedN desc ≡ 0
nd-desc = refl


-- MEMBERSHIP, at `Dec`.
dec-in : occursD 2 dup ≡ true
dec-in = refl

dec-out : occursD 7 dup ≡ false
dec-out = refl

dec-nowt-out : occursD 1 nowt ≡ false
dec-nowt-out = refl

may-in : occursM 2 dup ≡ true
may-in = refl

may-out : occursM 7 dup ≡ false
may-out = refl

-- ...and `ND` counts the occurrences, which is what `Occurs` being
-- proof-relevant was for.
nd-mult2 : multiplicity 2 dup ≡ 2
nd-mult2 = refl

nd-mult1 : multiplicity 5 dup ≡ 1
nd-mult1 = refl

nd-mult0 : multiplicity 7 dup ≡ 0
nd-mult0 = refl


-- THE PERMUTATION.  One bag, two representatives.
lo hi : List ℕ
lo = 1 ∷ 2 ∷ []
hi = 2 ∷ 1 ∷ []

-- `Occurs` cannot tell them apart, at any backend.
perm-dec-1 : occursD 1 lo ≡ occursD 1 hi
perm-dec-1 = refl

perm-dec-2 : occursD 2 lo ≡ occursD 2 hi
perm-dec-2 = refl

perm-mult-1 : multiplicity 1 lo ≡ multiplicity 1 hi
perm-mult-1 = refl

perm-mult-2 : multiplicity 2 lo ≡ multiplicity 2 hi
perm-mult-2 = refl

-- `Sorted` can, and does.
perm-sorted-lo : sortedD lo ≡ true
perm-sorted-lo = refl

perm-sorted-hi : sortedD hi ≡ false
perm-sorted-hi = refl


-- THE READOUT.  `Occurs` is proof-relevant, so the three answers read out
-- three different things from the same derivation.
import Theory.Instances.Bag.Chosen.Positions ℕ isSetℕ as P

positionOf firstAt : ℕ → List ℕ → Maybe ℕ
positionOf = P.positionOf discreteℕ
firstAt = P.firstAt discreteℕ

everyAt : ℕ → List ℕ → List ℕ
everyAt = P.everyAt discreteℕ

read-dec : positionOf 2 dup ≡ just 1
read-dec = refl

read-dec-out : positionOf 7 dup ≡ nothing
read-dec-out = refl

read-may : firstAt 2 dup ≡ just 1
read-may = refl

read-nd : everyAt 2 dup ≡ 1 ∷ 2 ∷ []
read-nd = refl

read-nd-out : everyAt 7 dup ≡ []
read-nd-out = refl

-- ...and the positions are positions in a REPRESENTATIVE.  The list moves
-- under the permutation; its length does not.
read-perm-lo : everyAt 1 lo ≡ 0 ∷ []
read-perm-lo = refl

read-perm-hi : everyAt 1 hi ≡ 1 ∷ []
read-perm-hi = refl

read-perm-len : length (everyAt 1 lo) ≡ length (everyAt 1 hi)
read-perm-len = refl
