{- Join two sorted halves around a pivot: recursion on the left half whose
   motive is the residual `⊸B` -- the right half is abstracted, not
   quantified.  löb on bag size rather than structural: a function-typed
   motive does not reduce through `μ`'s recursor; a löb family does. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Equality as Eq
open import Cubical.Data.Bool using (Bool ; true ; false)
open SortedSig
open SortedEqns
module Theory.Instances.Bags.Join
  (El : Type ℓ-zero) (isSetEl : isSet El) (le : El → El → Bool)
  (leTrans : (x y z : El) → le x y Eq.≡ true → le y z Eq.≡ true
           → le x z Eq.≡ true)
  where

open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Bags.Base El
open import Theory.Instances.Bags.Order El le
open import Theory.Instances.Bags.Rank El
open import Theory.Instances.Bags.Sorted.Base El le
open import Theory.Instances.Bags.Sorted.HLevels El isSetEl le
open import Theory.Type.Top.Base BagEqns El (λ _ → tt) closingPresentation

-- the pivot together with the sorted half above it
Pivot : El → TheoryTy _ tt
Pivot x = ⌈ ⌈gen x ⌉ ⌉ ⊎B (Sorted & Above x)

module _ (x : El) where
  private
    -- given the right half, the left half's sortedness extends to the whole
    JN : Fam _
    JN _ = (Sorted & Below x) ⇒ (Pivot x ⊸B Sorted)

    isSetJN : ∀ s m → isSet (JN s m)
    isSetJN _ m =
      isSetΠ λ _ → isSetΠ λ _ → isSetΠ λ _ → isSetΠ λ _ → isSetΠ λ _ →
      isSetΠ λ _ → isSetSorted _

  open Guarded▷ JN isSetJN

  private
    pivotAbove : (y : El) → le y x Eq.≡ true → Pivot x ⊢ Pivot x & Above y
    pivotAbove y w =
      ⊗-bagAll (aboveEl y)
      ∘⊢ ⊎Bmap (id⊢ ,& bagAll-gen (aboveEl y) x w)
               (id⊢ ,& (bagAll-mono (aboveEl x) (aboveEl y)
                         (λ z p → leTrans y x z w p) ∘⊢ π₂))

    nilJ : ⌈ εᵖ ⌉ ⊢ (Below x & ▷ tt) ⇒ (Pivot x ⊸B Sorted)
    -- the ε is absorbed into the pivot's own index, so the half above the
    -- pivot is never transported
    nilJ =
      ⇒-intro (⊸B-intro
        ( consSorted x
        ∘⊢ ⊎Bmap ⊎B-unitL⌈⌉ id⊢
        ∘⊢ ⊎B-assoc⁻
        ∘⊢ ⊎Bmap ⌈ε⌉→εB id⊢ )
        ∘⊢ π₁)

    consJ : (y : El)
      → ⌈ ⌈gen y ⌉ ⌉ ⊎B (Sorted & Above y)
      ⊢ (Below x & ▷ tt) ⇒ (Pivot x ⊸B Sorted)
    consJ y = ⇒-intro (⊸B-intro
      ( K-elim body
      ∘⊢ K-out
      ∘⊢ ⊎Bmap (bagAll-atGen (belowEl x) y) id⊢
      ∘⊢ ⊎B-assoc
      ∘⊢ ⊎Bmap pre id⊢ ))
      where
      pre : (⌈ ⌈gen y ⌉ ⌉ ⊎B (Sorted & Above y)) & (Below x & ▷ tt)
          ⊢ (⌈ ⌈gen y ⌉ ⌉ & Below x)
          ⊎B (((Sorted & Above y) & JN tt) & Below x)
      pre =
        bagAll-⊗ (belowEl x)
        ∘⊢ (▷-cons y ,&p id⊢)
        ∘⊢ ((π₁ ,& (π₂ ∘⊢ π₂)) ,& (π₁ ∘⊢ π₂))

      body : le y x Eq.≡ true
        → ⌈ ⌈gen y ⌉ ⌉
        ⊎B ((((Sorted & Above y) & JN tt) & Below x) ⊎B Pivot x)
        ⊢ Sorted
      body w = consSorted y ∘⊢ ⊎Bmap id⊢ (tailJ w)
        where
        tailJ : le y x Eq.≡ true
          → (((Sorted & Above y) & JN tt) & Below x) ⊎B Pivot x
          ⊢ Sorted & Above y
        tailJ w' =
          ((⊸B-app ∘⊢ ⊎Bmap ⇒-app id⊢) ,&p id⊢)
          ∘⊢ ⊗-bagAll (aboveEl y)
          ∘⊢ ⊎Bmap
              (((π₂ ∘⊢ π₁) ,& ((π₁ ∘⊢ π₁ ∘⊢ π₁) ,& π₂))
                ,& (π₂ ∘⊢ π₁ ∘⊢ π₁))
              (pivotAbove y w')

    stepJ : ∀ s → ▷ s ⊢ JN s
    stepJ tt =
      ⇒-intro (⇒-app
        ∘⊢ ((caseSorted nilJ consJ ∘⊢ π₁ ∘⊢ π₂)
             ,& ((π₂ ∘⊢ π₂) ,& π₁)))

  join : (Sorted & Below x) ⊎B Pivot x ⊢ Sorted
  join =
    ⊸B-intro⁻ (⇒-app ∘⊢ ((löb stepJ tt ∘⊢ ⊤Ty-intro) ,& id⊢))
