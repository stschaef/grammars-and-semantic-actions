-- Partition around a pivot, on arrangements.  `Halves x` is one tensor, so
-- there is nothing left to recombine.  `sideOf` is the only use of
-- `leTotal`: a map into a sum, eliminated rather than cased on.
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

Halves : El → TheoryTy _ tt
Halves x = (Seq & Below x) ⊎B (Seq & Above x)

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
    -- consing the head onto its own side pairs its comparison with the bound
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
