{- Sorted arrangements: `Seq`'s code with each tail bounded below by its
   head.  `recSorted` is its elim rule, in the same ⊎B coordinates. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open SortedSig
open SortedEqns
module Theory.Instances.Bags.Sorted.Base
  (El : Type ℓ-zero) (le : El → El → Bool) where

open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Unit using (Unit ; tt)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Bags.Base El
open import Theory.Instances.Bags.Order El le

private variable ℓA : Level

private
  consAtF : El → Fin 2 → Functor ℓM Unit (λ _ → tt) tt
  consAtF x = two (k ⌈ ⌈gen x ⌉ ⌉) (Var tt &e2 k (LiftTheoryTy ℓM (Above x)))

consAt : El → Functor ℓM Unit (λ _ → tt) tt
consAt x = ⊗e _⊙_ (consAtF x)

sortedBranch : Bool → Functor ℓM Unit (λ _ → tt) tt
sortedBranch false = k εB
sortedBranch true = ⊕e El consAt

SortedCode : Functor ℓM Unit (λ _ → tt) tt
SortedCode = ⊕e Bool sortedBranch

Sorted : TheoryTy (ℓF ℓM) tt
Sorted = μ {X = Unit} {xs = λ _ → tt} (λ _ → SortedCode) tt

private
  slots : ∀ {ℓC} (x : El) (C : TheoryTy ℓC tt) → Fin 2 → TheoryTy _ tt
  slots x C a = ⟦ consAtF x a ⟧TheoryTy (λ _ → C)

-- the layer, in ⊎B coordinates: the only place the code's shape is unpacked
module _ {ℓC ℓD} {C : TheoryTy ℓC tt} {D : TheoryTy ℓD tt}
  (n : ⌈ εᵖ ⌉ ⊢ D) (c : (x : El) → ⌈ ⌈gen x ⌉ ⌉ ⊎B (C & Above x) ⊢ D) where

  sortedLayer : ⟦ SortedCode ⟧TheoryTy (λ _ → C) ⊢ D
  sortedLayer = ⊕ᴰ-elim λ where
    false → n ∘⊢ εB→⌈ε⌉ ∘⊢ lowerTy
    true → ⊕ᴰ-elim λ x →
      c x ∘⊢ ⊎Bmap lowerTy (lowerTy ,&p (lowerTy ∘⊢ lowerTy))
           ∘⊢ ⊗ᵘ→⊎B (slots x C)

nilSorted : ⌈ εᵖ ⌉ ⊢ Sorted
nilSorted = roll ∘⊢ σ⊕ false ∘⊢ liftTy ∘⊢ ⌈ε⌉→εB

consSorted : (x : El) → ⌈ ⌈gen x ⌉ ⌉ ⊎B (Sorted & Above x) ⊢ Sorted
consSorted x =
  roll ∘⊢ σ⊕ true ∘⊢ σ⊕ x ∘⊢ ⊎B→⊗ᵘ (slots x Sorted)
  ∘⊢ ⊎Bmap liftTy (liftTy ,&p (liftTy ∘⊢ liftTy))

caseSorted : {C : TheoryTy ℓA tt}
  → ⌈ εᵖ ⌉ ⊢ C → ((x : El) → ⌈ ⌈gen x ⌉ ⌉ ⊎B (Sorted & Above x) ⊢ C)
  → Sorted ⊢ C
caseSorted n c = sortedLayer n c ∘⊢ unroll (λ _ → SortedCode) tt

recSorted : {C : TheoryTy ℓA tt}
  → ⌈ εᵖ ⌉ ⊢ C → ((x : El) → ⌈ ⌈gen x ⌉ ⌉ ⊎B (C & Above x) ⊢ C)
  → Sorted ⊢ C
recSorted n c = rec (λ _ → SortedCode) (λ _ → sortedLayer n c) tt

-- the underlying list of a sorted arrangement: forget every index
elements : Sorted ⊢ K (List El)
elements =
  recSorted (K-intro []) λ x → Kmap (x ∷_) ∘⊢ K-⊎B₂ ∘⊢ ⊎Bmap id⊢ π₁
