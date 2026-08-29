{-# OPTIONS --lossy-unification #-}
{- ⊗ distributes over set-indexed sums.

   In `Grammar.Distributivity` this is proved by hand, by unfolding the
   definition of ⊗ as a sigma of splittings. Here it is a formal
   consequence of the biclosure: `- ⊗ B` and `A ⊗ -` are left adjoints,
   so they preserve colimits. The proof uses nothing but the β/η laws
   of ⊕ᴰ, ⊸ and ⟜.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Semantics.Model

module Semantics.Distributivity {ℓ ℓ' ℓX} {Gen : hSet ℓX}
  (M : GrammarModel ℓ ℓ' ℓX Gen) where

open import Semantics.Notation M

private
  variable
    D : Grammar

module _ {X : hSet ℓX} {A : ⟨ X ⟩ → Grammar} {B : Grammar} where
  private
    A⊗B : ⟨ X ⟩ → Grammar
    A⊗B x = A x ⊗ B

    B⊗A : ⟨ X ⟩ → Grammar
    B⊗A x = B ⊗ A x

  ------------------------------------------------------------------
  -- Extensionality: a map out of (⊕ᴰ A) ⊗ B is determined by its
  -- restrictions along the coprojections. This is the ⊸-transpose of
  -- the corresponding fact for ⊕ᴰ.
  ------------------------------------------------------------------
  ⊗ᴰ≡ : {f f' : (⊕ᴰ A) ⊗ B ⊢ D}
      → (∀ x → f ∘g (σ x ,⊗ id) ≡ f' ∘g (σ x ,⊗ id))
      → f ≡ f'
  ⊗ᴰ≡ {f = f} {f' = f'} p = sym ⊸-β ∙ cong ⊸-intro⁻ q ∙ ⊸-β
    where
    q : ⊸-intro f ≡ ⊸-intro f'
    q = ⊕ᴰ≡ λ x →
      ⊸-intro-natural ∙ cong ⊸-intro (p x) ∙ sym ⊸-intro-natural

  ᴰ⊗≡ : {f f' : B ⊗ (⊕ᴰ A) ⊢ D}
      → (∀ x → f ∘g (id ,⊗ σ x) ≡ f' ∘g (id ,⊗ σ x))
      → f ≡ f'
  ᴰ⊗≡ {f = f} {f' = f'} p = sym ⟜-β ∙ cong ⟜-intro⁻ q ∙ ⟜-β
    where
    q : ⟜-intro f ≡ ⟜-intro f'
    q = ⊕ᴰ≡ λ x →
      ⟜-intro-natural ∙ cong ⟜-intro (p x) ∙ sym ⟜-intro-natural

  ------------------------------------------------------------------
  -- (⊕ᴰ A) ⊗ B ≅ ⊕ᴰ (λ x → A x ⊗ B)
  ------------------------------------------------------------------
  ⊕ᴰ-distR⁻ : ⊕ᴰ A⊗B ⊢ (⊕ᴰ A) ⊗ B
  ⊕ᴰ-distR⁻ = ⊕ᴰ-elim λ x → σ x ,⊗ id

  ⊕ᴰ-distR : (⊕ᴰ A) ⊗ B ⊢ ⊕ᴰ A⊗B
  ⊕ᴰ-distR = ⊸-intro⁻ (⊕ᴰ-elim λ x → ⊸-intro (σ {A = A⊗B} x))

  ⊕ᴰ-distR-β : ∀ x → ⊕ᴰ-distR ∘g (σ x ,⊗ id) ≡ σ {A = A⊗B} x
  ⊕ᴰ-distR-β x =
    ∘g-assoc ⊸-app _ _
    ∙ cong (⊸-app ∘g_) (,⊗-comp-l (σ x) _ ∙ cong (_,⊗ id) (⊕ᴰ-β _ x))
    ∙ ⊸-β

  ⊕ᴰ-distR-sec : ⊕ᴰ-distR ∘g ⊕ᴰ-distR⁻ ≡ id
  ⊕ᴰ-distR-sec = ⊕ᴰ≡ λ x →
    ∘g-assoc ⊕ᴰ-distR ⊕ᴰ-distR⁻ (σ x)
    ∙ cong (⊕ᴰ-distR ∘g_) (⊕ᴰ-β _ x)
    ∙ ⊕ᴰ-distR-β x
    ∙ sym (∘g-idL (σ x))

  ⊕ᴰ-distR-ret : ⊕ᴰ-distR⁻ ∘g ⊕ᴰ-distR ≡ id
  ⊕ᴰ-distR-ret = ⊗ᴰ≡ λ x →
    ∘g-assoc ⊕ᴰ-distR⁻ ⊕ᴰ-distR (σ x ,⊗ id)
    ∙ cong (⊕ᴰ-distR⁻ ∘g_) (⊕ᴰ-distR-β x)
    ∙ ⊕ᴰ-β _ x
    ∙ sym (∘g-idL (σ x ,⊗ id))

  ------------------------------------------------------------------
  -- B ⊗ (⊕ᴰ A) ≅ ⊕ᴰ (λ x → B ⊗ A x), by the other closure
  ------------------------------------------------------------------
  ⊕ᴰ-distL⁻ : ⊕ᴰ B⊗A ⊢ B ⊗ (⊕ᴰ A)
  ⊕ᴰ-distL⁻ = ⊕ᴰ-elim λ x → id ,⊗ σ x

  ⊕ᴰ-distL : B ⊗ (⊕ᴰ A) ⊢ ⊕ᴰ B⊗A
  ⊕ᴰ-distL = ⟜-intro⁻ (⊕ᴰ-elim λ x → ⟜-intro (σ {A = B⊗A} x))

  ⊕ᴰ-distL-β : ∀ x → ⊕ᴰ-distL ∘g (id ,⊗ σ x) ≡ σ {A = B⊗A} x
  ⊕ᴰ-distL-β x =
    ∘g-assoc ⟜-app _ _
    ∙ cong (⟜-app ∘g_) (,⊗-comp-r (σ x) _ ∙ cong (id ,⊗_) (⊕ᴰ-β _ x))
    ∙ ⟜-β

  ⊕ᴰ-distL-sec : ⊕ᴰ-distL ∘g ⊕ᴰ-distL⁻ ≡ id
  ⊕ᴰ-distL-sec = ⊕ᴰ≡ λ x →
    ∘g-assoc ⊕ᴰ-distL ⊕ᴰ-distL⁻ (σ x)
    ∙ cong (⊕ᴰ-distL ∘g_) (⊕ᴰ-β _ x)
    ∙ ⊕ᴰ-distL-β x
    ∙ sym (∘g-idL (σ x))

  ⊕ᴰ-distL-ret : ⊕ᴰ-distL⁻ ∘g ⊕ᴰ-distL ≡ id
  ⊕ᴰ-distL-ret = ᴰ⊗≡ λ x →
    ∘g-assoc ⊕ᴰ-distL⁻ ⊕ᴰ-distL (id ,⊗ σ x)
    ∙ cong (⊕ᴰ-distL⁻ ∘g_) (⊕ᴰ-distL-β x)
    ∙ ⊕ᴰ-β _ x
    ∙ sym (∘g-idL (id ,⊗ σ x))
