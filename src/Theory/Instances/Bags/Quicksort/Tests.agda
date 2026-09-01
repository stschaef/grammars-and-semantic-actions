{- Two pitfalls, recorded here (sites spread over Bags/Base, Inductive/Base,
   Join, Quicksort/Base):
   1. Never transport a payload whose type is a `μ`: `transp` transports the
      HIT index too, leaving a neutral no recursor matches -- `subst Sorted
      refl` is as bad as a real path.  Measured on a one-element `Sorted`:
      `elements m s` 0.7s, `elements m (subst Sorted refl s)` >45s.  Hence
      `join` absorbs its unit law into the pivot's index (`⊎B-unitL⌈⌉`).
   2. Never recurse through `μ`'s recursor at a function-typed motive:
      `rec` loops there; `join` recurses by `löb` on bag size instead.
   Both failures are data-dependent: `2 ∷ᵍ 1` and `1 ∷ᵍ 2` below separated
   under (1), so keep both. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Theory.Type.SemanticAction.Testing using (_↦_ ; _at_ ; passes ; Case)
open import Cubical.Foundations.Prelude
import Cubical.Data.Equality as Eq
open import Cubical.Data.Bool using (Bool ; true ; false)
module Theory.Instances.Bags.Quicksort.Tests where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ)

le : ℕ → ℕ → Bool
le zero _ = true
le (suc m) zero = false
le (suc m) (suc n) = le m n

leTotal : (x y : ℕ) → le x y Eq.≡ false → le y x Eq.≡ true
leTotal zero y ()
leTotal (suc x) zero p = Eq.refl
leTotal (suc x) (suc y) p = leTotal x y p

leTrans : (x y z : ℕ) → le x y Eq.≡ true → le y z Eq.≡ true → le x z Eq.≡ true
leTrans zero y z p q = Eq.refl
leTrans (suc x) zero z () q
leTrans (suc x) (suc y) zero p ()
leTrans (suc x) (suc y) (suc z) p q = leTrans x y z p q

open import Theory.Instances.Bags.Base ℕ
open import Theory.Instances.Bags.Sequence ℕ
open import Theory.Instances.Bags.Sorted.Base ℕ le
open import Theory.Instances.Bags.Quicksort.Base ℕ isSetℕ le leTotal leTrans

sort : {m : Bag} → Seq m → List ℕ
sort {m} s = elements m (quicksort m s)

_ : sort ([]ᵍ) ≡ []
_ = refl

_ : sort (3 ∷ᵍ []ᵍ) ≡ 3 ∷ []
_ = refl

-- pitfall 1 in miniature: `2 ∷ᵍ 1` leaves the transported half empty, `1 ∷ᵍ 2` not
_ : sort (2 ∷ᵍ 1 ∷ᵍ []ᵍ) ≡ 1 ∷ 2 ∷ []
_ = refl

_ : sort (1 ∷ᵍ 2 ∷ᵍ []ᵍ) ≡ 1 ∷ 2 ∷ []
_ = refl

_ : sort (3 ∷ᵍ 1 ∷ᵍ 2 ∷ᵍ []ᵍ) ≡ 1 ∷ 2 ∷ 3 ∷ []
_ = refl

_ : sort (2 ∷ᵍ 2 ∷ᵍ 1 ∷ᵍ []ᵍ) ≡ 1 ∷ 2 ∷ 2 ∷ []
_ = refl

_ : sort (5 ∷ᵍ 3 ∷ᵍ 8 ∷ᵍ 1 ∷ᵍ 2 ∷ᵍ []ᵍ) ≡ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ []
_ = refl

-- sorted/reverse-sorted: worst-case pivot, recursion `n` deep not `log n`
_ : sort (1 ∷ᵍ 2 ∷ᵍ 3 ∷ᵍ 4 ∷ᵍ 5 ∷ᵍ 6 ∷ᵍ 7 ∷ᵍ 8 ∷ᵍ []ᵍ)
  ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ []
_ = refl

_ : sort (8 ∷ᵍ 7 ∷ᵍ 6 ∷ᵍ 5 ∷ᵍ 4 ∷ᵍ 3 ∷ᵍ 2 ∷ᵍ 1 ∷ᵍ []ᵍ)
  ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ []
_ = refl

_ : sort ( 29 ∷ᵍ 10 ∷ᵍ 20 ∷ᵍ 11 ∷ᵍ 30 ∷ᵍ  6 ∷ᵍ  8 ∷ᵍ 23 ∷ᵍ
            1 ∷ᵍ 15 ∷ᵍ  9 ∷ᵍ 16 ∷ᵍ 24 ∷ᵍ 25 ∷ᵍ 22 ∷ᵍ 14 ∷ᵍ
           26 ∷ᵍ 28 ∷ᵍ  7 ∷ᵍ 17 ∷ᵍ 27 ∷ᵍ 19 ∷ᵍ 12 ∷ᵍ  4 ∷ᵍ
           18 ∷ᵍ  3 ∷ᵍ  2 ∷ᵍ 32 ∷ᵍ 13 ∷ᵍ  5 ∷ᵍ 31 ∷ᵍ 21 ∷ᵍ []ᵍ)
  ≡  1 ∷  2 ∷  3 ∷  4 ∷  5 ∷  6 ∷  7 ∷  8 ∷  9 ∷ 10 ∷ 11 ∷
    12 ∷ 13 ∷ 14 ∷ 15 ∷ 16 ∷ 17 ∷ 18 ∷ 19 ∷ 20 ∷ 21 ∷ 22 ∷
    23 ∷ 24 ∷ 25 ∷ 26 ∷ 27 ∷ 28 ∷ 29 ∷ 30 ∷ 31 ∷ 32 ∷ []
_ = refl

{- Measured ceiling: 64 shuffled ≈4s, 128 ≈65s, 256 >3min; worst-case pivot
   at 64 costs what a shuffle costs at 256.  Gradual slowdown is budget, not
   pitfall -- the pitfalls above hang at two elements. -}
