{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `recSeq`, by guarded recursion instead of by `Inductive/Base`'s `rec`.

   Same argument as `Sorted/Fold`: `rec` needs `{-# TERMINATING #-}` because
   its descent runs through `map (F x)`, and `Guarded/Base.fold` cannot
   replace it here because a bag's splitting says nothing about the size of
   its right half.  What pays is that the left slot of a cons is a
   generator, which is `Rank.▷-cons`.  The price is `isSet` of the motive. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Bags.Sequence.Fold
  (El : Type ℓ-zero) (isSetEl : isSet El) where

open import Cubical.Data.Unit using (tt ; tt*)
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Bags.Base El
open import Theory.Instances.Bags.Rank El
open import Theory.Instances.Bags.Sequence El
open import Theory.Instances.Bags.HLevels El isSetEl
open import Theory.Type.HLevels BagEqns El (λ _ → tt) closingPresentation
open import Theory.Type.Top.Base BagEqns El (λ _ → tt) closingPresentation

private variable ℓC : Level

module _ (C : TheoryTy ℓC tt) (isSetC : isSetTheoryTy C) where
  private
    Motive : Fam _
    Motive _ = Seq ⇒ C

    isSetMotive : ∀ s m → isSet (Motive s m)
    isSetMotive _ m = isSetΠ λ _ → isSetC m

  open Guarded▷ Motive isSetMotive

  module _ (n : ⌈ εᵖ ⌉ ⊢ C)
    (c : (x : El) → ⌈ ⌈gen x ⌉ ⌉ ⊎B C ⊢ C) where
    private
      layer : Seq ⊢ ▷ tt ⇒ C
      layer = caseSeq
        (⇒-intro (n ∘⊢ π₁))
        λ y → ⇒-intro
          (c y ∘⊢ ⊎Bmap id⊢ (⇒-app ∘⊢ &-swap) ∘⊢ ▷-cons y)

      step : ∀ s → ▷ s ⊢ Motive s
      step tt = ⇒-intro (⇒-app ∘⊢ &-swap ∘⊢ (id⊢ ,&p layer))

    recSeqg : Seq ⊢ C
    recSeqg = ⇒-app ∘⊢ ((löb step tt ∘⊢ ⊤Ty-intro) ,& id⊢)

-- Left unit for arrangements.  `⊎B-unitL` is `subst A` at the payload, and
-- at `A = Seq` that is pitfall 1 of `Quicksort/Tests`: the index lives in
-- the free model, so the transported arrangement goes neutral and the fold
-- over it never fires.  It is data-dependent -- an empty right half
-- transports fine -- so it reads as working until it does not.
--
-- Same remedy as `Join.nilJ`: keep the ε a code and push it down to the
-- leaf, where the payload is `⌈ εᵖ ⌉` too and `⊎B-unitL⌈⌉` is a path in
-- `Bag` rather than a transport.  The arrangement is rebuilt cons by cons
-- instead of moved, which costs a traversal and computes.
unitLSeq : ⌈ εᵖ ⌉ ⊎B Seq ⊢ Seq
unitLSeq =
  ⊸B-intro⁻
    (recSeqg (⌈ εᵖ ⌉ ⊸B Seq) (isSet⊸B {A = ⌈ εᵖ ⌉} {B = Seq} isSetSeq)
      atNil atCons)
  ∘⊢ ⊎B-comm
  where
  atNil : ⌈ εᵖ ⌉ ⊢ ⌈ εᵖ ⌉ ⊸B Seq
  atNil = ⊸B-intro {A = ⌈ εᵖ ⌉} {B = ⌈ εᵖ ⌉} {C = Seq}
            (nilSeq ∘⊢ ⊎B-unitL⌈⌉ ∘⊢ ⊎Bmap ⌈ε⌉→εB id⊢)

  atCons : (x : El) → ⌈ ⌈gen x ⌉ ⌉ ⊎B (⌈ εᵖ ⌉ ⊸B Seq) ⊢ ⌈ εᵖ ⌉ ⊸B Seq
  atCons x =
    ⊸B-intro {A = ⌈ ⌈gen x ⌉ ⌉ ⊎B (⌈ εᵖ ⌉ ⊸B Seq)} {B = ⌈ εᵖ ⌉} {C = Seq}
      ( consSeq x
      ∘⊢ ⊎Bmap (id⊢ {A = ⌈ ⌈gen x ⌉ ⌉}) (⊸B-app {A = ⌈ εᵖ ⌉} {B = Seq})
      ∘⊢ ⊎B-assoc {A = ⌈ ⌈gen x ⌉ ⌉} {B = ⌈ εᵖ ⌉ ⊸B Seq} {C = ⌈ εᵖ ⌉} )

-- Concatenation.  The motive is the residual, so the recursion on the left
-- arrangement carries the right one along; `⊸B-intro⁻` reads it back as a
-- map out of the tensor.
appendSeq : Seq ⊎B Seq ⊢ Seq
appendSeq =
  ⊸B-intro⁻ (recSeqg (Seq ⊸B Seq) (isSet⊸B {A = Seq} {B = Seq} isSetSeq) atNil atCons)
  where
  atNil : ⌈ εᵖ ⌉ ⊢ Seq ⊸B Seq
  atNil = ⊸B-intro {A = ⌈ εᵖ ⌉} {B = Seq} {C = Seq} unitLSeq

  atCons : (x : El) → ⌈ ⌈gen x ⌉ ⌉ ⊎B (Seq ⊸B Seq) ⊢ Seq ⊸B Seq
  atCons x =
    ⊸B-intro {A = ⌈ ⌈gen x ⌉ ⌉ ⊎B (Seq ⊸B Seq)} {B = Seq} {C = Seq}
      ( consSeq x
      ∘⊢ ⊎Bmap (id⊢ {A = ⌈ ⌈gen x ⌉ ⌉}) (⊸B-app {A = Seq} {B = Seq})
      ∘⊢ ⊎B-assoc {A = ⌈ ⌈gen x ⌉ ⌉} {B = Seq ⊸B Seq} {C = Seq} )

infixr 5 _++ᵍ_
_++ᵍ_ : {a b : Bag} → Seq a → Seq b → Seq (a ⊙ᵖ b)
_++ᵍ_ {a} {b} s t = appendSeq (a ⊙ᵖ b) (two a b , Eq.refl , (s , t , tt*))
