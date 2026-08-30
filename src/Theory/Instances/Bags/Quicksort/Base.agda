{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Equality as Eq
open import Cubical.Data.Bool using (Bool ; true ; false)
open SortedSig
open SortedEqns
module Theory.Instances.Bags.Quicksort.Base
  (El : Type ℓ-zero) (isSetEl : isSet El) (le : El → El → Bool)
  (leTotal : (x y : El) → le x y Eq.≡ false → le y x Eq.≡ true)
  (leTrans : (x y z : El) → le x y Eq.≡ true → le y z Eq.≡ true
           → le x z Eq.≡ true)
  where

open import Cubical.Data.FinData using (Fin) renaming (zero to fzero ; suc to fsuc)
open import Cubical.Data.Unit using (tt ; tt*)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Bags.Base El
open import Theory.Instances.Bags.Order El le
open import Theory.Instances.Bags.Rank El
open import Theory.Instances.Bags.Sequence El
open import Theory.Instances.Bags.Generation El isSetEl using (arrange)
open import Theory.Instances.Bags.Sorted.Base El le
open import Theory.Instances.Bags.Sorted.HLevels El isSetEl le
open import Theory.Instances.Bags.Partition El isSetEl le leTotal
open import Theory.Instances.Bags.Join El isSetEl le leTrans
open import Theory.Type.Top.Base BagEqns El (λ _ → tt) closingPresentation

private
  QS : Fam _
  QS _ = Seq ⇒ Sorted

  isSetQS : ∀ s m → isSet (QS s m)
  isSetQS _ m = isSetΠ λ _ → isSetSorted m

open Guarded▷ QS isSetQS

private
  sortHalf : {P : TheoryTy ℓ-zero tt} → (Seq & P) & QS tt ⊢ Sorted & P
  sortHalf = (⇒-app ∘⊢ (π₂ ,& (π₁ ∘⊢ π₁))) ,& (π₂ ∘⊢ π₁)

  qs : Seq ⊢ ▷ tt ⇒ Sorted
  qs = caseSeq
    (⇒-intro (nilSorted ∘⊢ π₁))
    λ y → ⇒-intro
      ( join y
      ∘⊢ ⊎B-assoc
      ∘⊢ ⊎Bmap ⊎B-comm id⊢
      ∘⊢ ⊎B-assoc⁻
      ∘⊢ ⊎Bmap id⊢ (⊎Bmap sortHalf sortHalf)
      ∘⊢ ▷-split y
      ∘⊢ (⊎Bmap id⊢ (partSeq y) ,&p id⊢) )

  step : ∀ s → ▷ s ⊢ QS s
  step tt = ⇒-intro (⇒-app ∘⊢ &-swap ∘⊢ (id⊢ ,&p qs))

quicksort : Seq ⊢ Sorted
quicksort = ⇒-app ∘⊢ ((löb step tt ∘⊢ ⊤Ty-intro) ,& id⊢)

-- Every bag can be sorted.  `quicksort` sorts an *arrangement*; `arrange`
-- supplies one -- merely, since a bag has many and no canonical one -- and
-- the composite is the statement about bags that the sorter alone is not.
sortBag : (m : Bag) → ∥ Sorted m ∥₁
sortBag m = PT.map (quicksort m) (arrange m)
