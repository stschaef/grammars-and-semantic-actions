{- `Seq m`: the bag `m`, arranged as a sequence -- the internal form of
   `Σ[ xs ∈ List El ] (bag xs ≡ m)`, and what quicksort consumes.
   `recSeq`/`caseSeq` are its intro and elim rules; downstream files never
   see the code's `⊗ᵘ` shape. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open SortedSig
open SortedEqns
module Theory.Instances.Bags.Sequence (El : Type ℓ-zero) where

import Cubical.Data.Equality as Eq
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Bags.Base El

private variable ℓA : Level

private
  atSeqF : El → Fin 2 → Functor ℓM Unit (λ _ → tt) tt
  atSeqF x = two (k ⌈ ⌈gen x ⌉ ⌉) (Var tt)

atSeq : El → Functor ℓM Unit (λ _ → tt) tt
atSeq x = ⊗e _⊙_ (atSeqF x)

seqBranch : Bool → Functor ℓM Unit (λ _ → tt) tt
seqBranch false = k εB
seqBranch true = ⊕e El atSeq

SeqCode : Functor ℓM Unit (λ _ → tt) tt
SeqCode = ⊕e Bool seqBranch

Seq : TheoryTy (ℓF ℓM) tt
Seq = μ {X = Unit} {xs = λ _ → tt} (λ _ → SeqCode) tt

private
  -- the two slots of `atSeq x`, as the uniform tuple the code produces
  slots : ∀ {ℓC} (x : El) (C : TheoryTy ℓC tt) → Fin 2 → TheoryTy _ tt
  slots x C a = ⟦ atSeqF x a ⟧TheoryTy (λ _ → C)

-- the layer, in ⊎B coordinates: this is the only place the code's shape
-- is unpacked
module _ {ℓC ℓD} {C : TheoryTy ℓC tt} {D : TheoryTy ℓD tt}
  (n : ⌈ εᵖ ⌉ ⊢ D) (c : (x : El) → ⌈ ⌈gen x ⌉ ⌉ ⊎B C ⊢ D) where

  seqLayer : ⟦ SeqCode ⟧TheoryTy (λ _ → C) ⊢ D
  seqLayer = ⊕ᴰ-elim λ where
    false → n ∘⊢ εB→⌈ε⌉ ∘⊢ lowerTy
    true → ⊕ᴰ-elim λ x →
      c x ∘⊢ ⊎Bmap lowerTy lowerTy ∘⊢ ⊗ᵘ→⊎B (slots x C)

nilSeq : ⌈ εᵖ ⌉ ⊢ Seq
nilSeq = roll ∘⊢ σ⊕ false ∘⊢ liftTy ∘⊢ ⌈ε⌉→εB

consSeq : (x : El) → ⌈ ⌈gen x ⌉ ⌉ ⊎B Seq ⊢ Seq
consSeq x =
  roll ∘⊢ σ⊕ true ∘⊢ σ⊕ x
  ∘⊢ ⊎B→⊗ᵘ (slots x Seq) ∘⊢ ⊎Bmap liftTy liftTy

caseSeq : {C : TheoryTy ℓA tt}
  → ⌈ εᵖ ⌉ ⊢ C → ((x : El) → ⌈ ⌈gen x ⌉ ⌉ ⊎B Seq ⊢ C)
  → Seq ⊢ C
caseSeq n c = seqLayer n c ∘⊢ unroll (λ _ → SeqCode) tt

[]ᵍ : Seq εᵖ
[]ᵍ = nilSeq εᵖ Eq.refl

infixr 5 _∷ᵍ_
_∷ᵍ_ : (x : El) {m : Bag} → Seq m → Seq (⌈gen x ⌉ ⊙ᵖ m)
_∷ᵍ_ x {m} s =
  consSeq x (⌈gen x ⌉ ⊙ᵖ m) (two ⌈gen x ⌉ m , Eq.refl , (Eq.refl , s , tt*))

-- One element, arranged.  Written with the unitor rather than by
-- transporting `x ∷ᵍ []ᵍ` along `⊙-unitR`, because a `subst` at a `μ` does
-- not reduce -- see the header of `Quicksort/Tests`.
singletonSeq : (x : El) → ⌈ ⌈gen x ⌉ ⌉ ⊢ Seq
singletonSeq x =
  consSeq x ∘⊢ ⊎Bmap id⊢ (nilSeq ∘⊢ εB→⌈ε⌉) ∘⊢ ⊎B-unitR⁻

singleᵍ : (x : El) → Seq ⌈gen x ⌉
singleᵍ x = singletonSeq x ⌈gen x ⌉ Eq.refl
