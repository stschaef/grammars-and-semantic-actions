{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `recSorted`, by guarded recursion instead of by `Inductive/Base`'s `rec`.

   `rec` carries a `{-# TERMINATING #-}`: its descent runs through
   `map (F x)`, which the checker cannot see into.  `Guarded/Base.fold`
   removes that in general, but not here -- it wants a `Guard` derived from
   the splitting alone, and a splitting of a bag says nothing about the size
   of its right half.  What pays here is that the *left* slot of a cons is a
   generator, hence one element, and that is exactly `Rank.▷-cons`.

   So the recursion is `löb` at the family `Sorted ⇒ C`, which is a term:
   nothing is asserted, and the price is `isSet` of the motive. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open import Cubical.Data.Bool using (Bool)
open SortedSig
open SortedEqns
module Theory.Instances.Bags.Sorted.Fold
  (El : Type ℓ-zero) (isSetEl : isSet El) (le : El → El → Bool) where

open import Cubical.Data.List using (List ; [] ; _∷_ ; isOfHLevelList)
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Bags.Base El
open import Theory.Instances.Bags.Order El le
open import Theory.Instances.Bags.Rank El
open import Theory.Instances.Bags.Sorted.Base El le
open import Theory.Type.HLevels BagEqns El (λ _ → tt) closingPresentation
open import Theory.Type.Top.Base BagEqns El (λ _ → tt) closingPresentation

private variable ℓC : Level

module _ (C : TheoryTy ℓC tt) (isSetC : isSetTheoryTy C) where
  private
    Motive : Fam _
    Motive _ = Sorted ⇒ C

    isSetMotive : ∀ s m → isSet (Motive s m)
    isSetMotive _ m = isSetΠ λ _ → isSetC m

  open Guarded▷ Motive isSetMotive

  module _ (n : ⌈ εᵖ ⌉ ⊢ C)
    (c : (x : El) → ⌈ ⌈gen x ⌉ ⌉ ⊎B (C & Above x) ⊢ C) where
    private
      -- the tail, folded, with its bound carried past the recursive call
      foldTail : {x : El}
        → (Sorted & Above x) & Motive tt ⊢ C & Above x
      foldTail = (⇒-app ∘⊢ (π₂ ,& (π₁ ∘⊢ π₁))) ,& (π₂ ∘⊢ π₁)

      layer : Sorted ⊢ ▷ tt ⇒ C
      layer = caseSorted
        (⇒-intro (n ∘⊢ π₁))
        λ y → ⇒-intro (c y ∘⊢ ⊎Bmap id⊢ foldTail ∘⊢ ▷-cons y)

      step : ∀ s → ▷ s ⊢ Motive s
      step tt = ⇒-intro (⇒-app ∘⊢ &-swap ∘⊢ (id⊢ ,&p layer))

    recSortedg : Sorted ⊢ C
    recSortedg = ⇒-app ∘⊢ ((löb step tt ∘⊢ ⊤Ty-intro) ,& id⊢)

-- ...and the readback, which is the one place quicksort's answer leaves the
-- theory.  `K (List El)` is a set because `El` is.
elementsg : Sorted ⊢ K (List El)
elementsg =
  recSortedg (K (List El)) (λ _ → isOfHLevelList 0 isSetEl)
    (K-intro []) λ x → Kmap (x ∷_) ∘⊢ K-⊎B₂ ∘⊢ ⊎Bmap id⊢ π₁
