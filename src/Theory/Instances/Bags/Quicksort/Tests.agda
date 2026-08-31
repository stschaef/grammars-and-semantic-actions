{- Quicksort at a concrete alphabet.  `Quicksort` is parameterised by `El`
   and the comparison, so the evaluation tests have to live here.

   These are the tests that stopped the pipeline evaluating twice, so the
   two pitfalls are recorded here rather than at the sites, which are spread
   over `Bags/Base`, `Inductive/Base`, `Join` and `Quicksort/Base`.

   1. Do not transport a payload whose type is a `μ`.

      `transp` at an indexed data family transports the *index* as well, and
      the index here lives in the free-model HIT, so what lands there is a
      neutral `comp (λ i → ↓M tt) …`.  A recursor whose argument is neutral
      never matches `roll`, so everything underneath goes stuck.  This does
      not need a stuck path: `subst Sorted refl` is exactly as bad as
      `subst Sorted (sym (⊙-unitL _))`.  Measured on a ONE-element `Sorted`,
      `elements m s` is 0.7s and `elements m (subst Sorted refl s)` is over
      45s.  `unroll`/`caseSorted` still fire -- they only want the head
      constructor -- so the symptom is that a case analysis works and the
      fold over the same value does not.

      That is why `join` absorbs its unit law into the pivot's own index
      (`⊎B-unitL⌈⌉`, a path in `Bag`) instead of moving the `Pivot` bundle
      with `⊎B-unitL`.  Any body written with `subst Sorted` pays the same
      cost, however structural its recursion.  `⊎B-assoc`/`⊎B-comm`
      repackage rather than transport and are fine; so are the substs at
      `bagAll p` and at the ℕ-order, which are props.

      To tell this apart from anything else, A/B one value: read it, then
      read it again after `subst A refl`.

   2. Do not recurse through `μ`'s recursor at a function-typed motive.

      `rec` loops there rather than reducing.  `join`'s motive is
      `(Sorted & Below x) ⇒ (Pivot x ⊸B Sorted)`, so it recurses by `löb` on
      bag size, whose families may be function-typed, even though the
      recursion *is* structural on the left half.

   Both failures are data-dependent, which makes them easy to misread as
   working: a test whose transported half happens to be empty, or whose
   recursion happens to bottom out at `nil`, passes.  `2 ∷ᵍ 1` and `1 ∷ᵍ 2`
   below separated under (1) for exactly that reason, so keep both. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
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

-- read the sorted arrangement back off as a list
sort : {m : Bag} → Seq m → List ℕ
sort {m} s = elements m (quicksort m s)

_ : sort ([]ᵍ) ≡ []
_ = refl

_ : sort (3 ∷ᵍ []ᵍ) ≡ 3 ∷ []
_ = refl

-- pitfall 1 in miniature: `2 ∷ᵍ 1` leaves the transported half empty and
-- `1 ∷ᵍ 2` does not, so only the second one used to hang
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

-- already sorted and reverse sorted: the pivot choice is worst case, so the
-- recursion is `n` deep rather than `log n`
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

{- Measured ceiling, past what is checked above: 64 shuffled elements is
   about 4s, 128 about 65s, 256 over 3 minutes, and a worst-case pivot
   sequence costs at 64 what a shuffle costs at 256.  Superlinear, but a
   budget rather than a block -- which is the distinction to make before
   assuming a regression is one of the two pitfalls above.  Neither of those
   is gradual: they hang at two elements. -}
