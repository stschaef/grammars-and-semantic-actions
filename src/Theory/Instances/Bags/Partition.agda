{- Partition around a pivot, on arrangements.  `Halves x` is one tensor, so
   the splitting of the bag, the two bounds and the two arrangements come out
   together -- there is nothing left to recombine, and no `lo`/`hi` to relate
   back to the whole.

   `sideOf` is the decision, and the only place `leTotal` is used: it is a
   map into a sum, so the algebra below eliminates it rather than casing. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Equality as Eq
open import Cubical.Data.Bool using (Bool ; true ; false)
open SortedSig
open SortedEqns
module Theory.Instances.Bags.Partition
  (El : Type ℓ-zero) (isSetEl : isSet El) (le : El → El → Bool)
  (leTotal : (x y : El) → le x y Eq.≡ false → le y x Eq.≡ true)
  where

open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Bags.Base El
open import Theory.Instances.Bags.Order El le
open import Theory.Instances.Bags.Sequence El
open import Theory.Instances.Bags.Sequence.Fold El isSetEl
open import Theory.Instances.Bags.HLevels El isSetEl
open import Theory.Type.HLevels BagEqns El (λ _ → tt) closingPresentation

Halves : El → TheoryTy _ tt
Halves x = (Seq & Below x) ⊎B (Seq & Above x)

isSetHalves : (x : El) → isSetTheoryTy (Halves x)
isSetHalves x =
  isSet⊎B (isSet& isSetSeq (isSetBelow x)) (isSet& isSetSeq (isSetAbove x))

-- The head, sorted against the pivot.  `le` is a metalanguage function --
-- the theory of bags has no order -- so consulting it is a step outside
-- the DSL, and this is the only place it happens.  What crosses back in is
-- a sum, so every caller eliminates it rather than casing on a `Bool`.
SideOf : El → El → TheoryTy _ tt
SideOf x y =
  (⌈ ⌈gen y ⌉ ⌉ & bagAll (belowEl x)) ⊕ (⌈ ⌈gen y ⌉ ⌉ & bagAll (aboveEl x))

sideOf : (x y : El) → ⌈ ⌈gen y ⌉ ⌉ ⊢ SideOf x y
sideOf x y = onCompare (le y x) Eq.refl
  where
  onCompare : (b : Bool) → le y x Eq.≡ b → ⌈ ⌈gen y ⌉ ⌉ ⊢ SideOf x y
  onCompare true w = inl ∘⊢ (id⊢ ,& bagAll-gen (belowEl x) y w)
  onCompare false w =
    inr ∘⊢ (id⊢ ,& bagAll-gen (aboveEl x) y (leTotal y x w))

partSeq : (x : El) → Seq ⊢ Halves x
partSeq x = recSeqg (Halves x) (isSetHalves x) nilCase consCase
  where
  nilCase : ⌈ εᵖ ⌉ ⊢ Halves x
  nilCase =
    ⊎Bmap ((nilSeq ,& bagAll-ε (belowEl x)) ∘⊢ εB→⌈ε⌉)
          (nilSeq ,& bagAll-ε (aboveEl x))
    ∘⊢ ⊎B-unitL⁻

  consCase : (y : El) → ⌈ ⌈gen y ⌉ ⌉ ⊎B Halves x ⊢ Halves x
  consCase y =
    ⊕-elim putBelow putAbove ∘⊢ ⊎B⊕-dist ∘⊢ ⊎Bmap (sideOf x y) id⊢
    where
    -- `bagAll` is a fold, so consing the head onto its own side just pairs
    -- the head's comparison with the half's bound
    consInto : (p : El → hProp ℓ-zero)
      → (⌈ ⌈gen y ⌉ ⌉ & bagAll p) ⊎B (Seq & bagAll p) ⊢ Seq & bagAll p
    consInto p = (consSeq y ,&p id⊢) ∘⊢ ⊗-bagAll p

    putBelow : (⌈ ⌈gen y ⌉ ⌉ & bagAll (belowEl x)) ⊎B Halves x ⊢ Halves x
    putBelow = ⊎Bmap (consInto (belowEl x)) id⊢ ∘⊢ ⊎B-assoc⁻

    putAbove : (⌈ ⌈gen y ⌉ ⌉ & bagAll (aboveEl x)) ⊎B Halves x ⊢ Halves x
    putAbove =
      ⊎B-comm
      ∘⊢ ⊎Bmap (consInto (aboveEl x)) id⊢
      ∘⊢ ⊎B-assoc⁻
      ∘⊢ ⊎Bmap id⊢ ⊎B-comm
