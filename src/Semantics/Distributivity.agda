{-# OPTIONS --lossy-unification #-}
{- ⊗ distributes over set-indexed sums.

   In `Grammar.Sum.Properties` this is proved by hand, by unfolding ⊗
   into a sigma of splittings. Here both directions are instances of
   one theorem — `Semantics.Structure.Preservation`, that a left
   adjoint preserves set-indexed coproducts — applied to the two
   partial applications of the tensor, whose right adjoints are ⊸ and
   ⟜ respectively.

   Nothing here is specific to ⊗: for the same statement about an
   arbitrary operation of an arbitrary algebraic theory, in an
   arbitrary argument slot, see `ClosedOps.op-dist` in
   `Semantics.Structure.Operation`.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Semantics.Model

module Semantics.Distributivity {ℓ ℓ' ℓX} {Gen : hSet ℓX}
  (M : GrammarModel ℓ ℓ' ℓX Gen) where

open import Semantics.Notation M
open import Semantics.Structure.Biclosed
open import Semantics.Structure.Preservation

module _ {X : hSet ℓX} {A : ⟨ X ⟩ → Grammar} {B : Grammar} where
  private
    A⊗B : ⟨ X ⟩ → Grammar
    A⊗B x = A x ⊗ B

    B⊗A : ⟨ X ⟩ → Grammar
    B⊗A x = B ⊗ A x

    -- (- ⊗ B) is a left adjoint, with right adjoint B ⊸ -
    module L = PreserveΣ (tensorR MC B) (⊸ues B) (Σs X A) (Σs X A⊗B)
    -- (B ⊗ -) is a left adjoint, with right adjoint - ⟜ B
    module R = PreserveΣ (tensorL MC B) (⟜ues B) (Σs X A) (Σs X B⊗A)

  ------------------------------------------------------------------
  -- Extensionality: a map out of a tensor with a coproduct is
  -- determined by its restrictions along the coprojections.
  ------------------------------------------------------------------
  ⊗ᴰ≡ : {D : Grammar} {f f' : (⊕ᴰ A) ⊗ B ⊢ D}
      → (∀ x → f ∘g (σ x ,⊗ id) ≡ f' ∘g (σ x ,⊗ id))
      → f ≡ f'
  ⊗ᴰ≡ = L.E⊕ext

  ᴰ⊗≡ : {D : Grammar} {f f' : B ⊗ (⊕ᴰ A) ⊢ D}
      → (∀ x → f ∘g (id ,⊗ σ x) ≡ f' ∘g (id ,⊗ σ x))
      → f ≡ f'
  ᴰ⊗≡ = R.E⊕ext

  ------------------------------------------------------------------
  -- (⊕ᴰ A) ⊗ B ≅ ⊕ᴰ (λ x → A x ⊗ B): sum on the left
  ------------------------------------------------------------------
  ⊕ᴰ-distL⁻ : ⊕ᴰ A⊗B ⊢ (⊕ᴰ A) ⊗ B
  ⊕ᴰ-distL⁻ = L.preserve⁻

  ⊕ᴰ-distL : (⊕ᴰ A) ⊗ B ⊢ ⊕ᴰ A⊗B
  ⊕ᴰ-distL = L.preserve

  ⊕ᴰ-distL-β : ∀ x → ⊕ᴰ-distL ∘g (σ x ,⊗ id) ≡ σ {A = A⊗B} x
  ⊕ᴰ-distL-β = L.preserve-β

  ⊕ᴰ-distL-sec : ⊕ᴰ-distL ∘g ⊕ᴰ-distL⁻ ≡ id
  ⊕ᴰ-distL-sec = L.preserve-sec

  ⊕ᴰ-distL-ret : ⊕ᴰ-distL⁻ ∘g ⊕ᴰ-distL ≡ id
  ⊕ᴰ-distL-ret = L.preserve-ret

  ------------------------------------------------------------------
  -- B ⊗ (⊕ᴰ A) ≅ ⊕ᴰ (λ x → B ⊗ A x): sum on the right
  ------------------------------------------------------------------
  ⊕ᴰ-distR⁻ : ⊕ᴰ B⊗A ⊢ B ⊗ (⊕ᴰ A)
  ⊕ᴰ-distR⁻ = R.preserve⁻

  ⊕ᴰ-distR : B ⊗ (⊕ᴰ A) ⊢ ⊕ᴰ B⊗A
  ⊕ᴰ-distR = R.preserve

  ⊕ᴰ-distR-β : ∀ x → ⊕ᴰ-distR ∘g (id ,⊗ σ x) ≡ σ {A = B⊗A} x
  ⊕ᴰ-distR-β = R.preserve-β

  ⊕ᴰ-distR-sec : ⊕ᴰ-distR ∘g ⊕ᴰ-distR⁻ ≡ id
  ⊕ᴰ-distR-sec = R.preserve-sec

  ⊕ᴰ-distR-ret : ⊕ᴰ-distR⁻ ∘g ⊕ᴰ-distR ≡ id
  ⊕ᴰ-distR-ret = R.preserve-ret
