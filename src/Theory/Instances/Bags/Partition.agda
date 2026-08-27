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
  (El : Type ℓ-zero) (le : El → El → Bool)
  (leTotal : (x y : El) → le x y Eq.≡ false → le y x Eq.≡ true)
  where

open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Bags.Base El
open import Theory.Instances.Bags.Order El le
open import Theory.Instances.Bags.Sequence El

-- an arrangement split in two, each half bounded by the pivot
Halves : El → TheoryTy _ tt
Halves x = (Seq & Below x) ⊎B (Seq & Above x)

-- which side of the pivot a generator falls on
side : El → Bool → El → hProp ℓ-zero
side x true = belowEl x
side x false = aboveEl x

sideOf : (x y : El)
  → ⌈ ⌈gen y ⌉ ⌉ ⊢ ⊕[ b ∈ Bool ] (⌈ ⌈gen y ⌉ ⌉ & bagAll (side x b))
sideOf x y = go (le y x) Eq.refl
  where
  go : (b : Bool) → le y x Eq.≡ b
     → ⌈ ⌈gen y ⌉ ⌉ ⊢ ⊕[ b' ∈ Bool ] (⌈ ⌈gen y ⌉ ⌉ & bagAll (side x b'))
  go true w = σ⊕ true ∘⊢ (id⊢ ,& bagAll-gen (belowEl x) y w)
  go false w = σ⊕ false ∘⊢ (id⊢ ,& bagAll-gen (aboveEl x) y (leTotal y x w))

partSeq : (x : El) → Seq ⊢ Halves x
partSeq x = recSeq nilCase consCase
  where
  nilCase : ⌈ εᵖ ⌉ ⊢ Halves x
  nilCase =
    ⊎Bmap ((nilSeq ,& bagAll-ε (belowEl x)) ∘⊢ εB→⌈ε⌉)
          (nilSeq ,& bagAll-ε (aboveEl x))
    ∘⊢ ⊎B-unitL⁻

  consCase : (y : El) → ⌈ ⌈gen y ⌉ ⌉ ⊎B Halves x ⊢ Halves x
  consCase y = ⊕ᴰ-elim put ∘⊢ ⊎B⊕ᴰ-dist ∘⊢ ⊎Bmap (sideOf x y) id⊢
    where
    -- `bagAll` is a fold, so consing the head onto its own side just pairs
    -- the head's comparison with the half's bound
    consInto : (p : El → hProp ℓ-zero)
      → (⌈ ⌈gen y ⌉ ⌉ & bagAll p) ⊎B (Seq & bagAll p) ⊢ Seq & bagAll p
    consInto p = (consSeq y ,&p id⊢) ∘⊢ ⊗-bagAll p

    put : (b : Bool)
      → (⌈ ⌈gen y ⌉ ⌉ & bagAll (side x b)) ⊎B Halves x ⊢ Halves x
    put true = ⊎Bmap (consInto (belowEl x)) id⊢ ∘⊢ ⊎B-assoc⁻
    put false =
      ⊎B-comm
      ∘⊢ ⊎Bmap (consInto (aboveEl x)) id⊢
      ∘⊢ ⊎B-assoc⁻
      ∘⊢ ⊎Bmap id⊢ ⊎B-comm
