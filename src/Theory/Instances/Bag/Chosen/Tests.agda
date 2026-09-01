{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `[ 1 , 2 ]` and `[ 2 , 1 ]` are the SAME BAG (`Quotient`'s `toBag-swap`):
   `Occurs` answers the same at all three backends; `Sorted` differs, so it
   is not a predicate on bags.  All tests are `refl`. -}
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

-- boolean order, so everything reduces
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


nowt asc dup desc plateau : List ℕ
nowt = []
asc = 1 ∷ 2 ∷ 5 ∷ []
dup = 1 ∷ 2 ∷ 2 ∷ 5 ∷ []
desc = 5 ∷ 2 ∷ 1 ∷ []
plateau = 3 ∷ 3 ∷ []


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

-- `Maybe` agrees; nothing to commit to, one rule per head.
may-asc : sortedM asc ≡ true
may-asc = refl

may-desc : sortedM desc ≡ false
may-desc = refl

-- `ND` finds exactly one derivation: `Sorted` is a proposition.
nd-asc : sortedN asc ≡ 1
nd-asc = refl

nd-desc : sortedN desc ≡ 0
nd-desc = refl


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

-- `ND` counts occurrences: what `Occurs` being proof-relevant was for.
nd-mult2 : multiplicity 2 dup ≡ 2
nd-mult2 = refl

nd-mult1 : multiplicity 5 dup ≡ 1
nd-mult1 = refl

nd-mult0 : multiplicity 7 dup ≡ 0
nd-mult0 = refl


-- One bag, two representatives.
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


-- `Occurs` is proof-relevant: three answers read three different things
-- from the same derivation.
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

-- positions are in a REPRESENTATIVE: the list moves, its length does not
read-perm-lo : everyAt 1 lo ≡ 0 ∷ []
read-perm-lo = refl

read-perm-hi : everyAt 1 hi ≡ 1 ∷ []
read-perm-hi = refl

read-perm-len : length (everyAt 1 lo) ≡ length (everyAt 1 hi)
read-perm-len = refl
