{-# OPTIONS --lossy-unification #-}
{- Coproduct of a family of objects X → C .ob indexed by a type X.

   This is the exact dual of `Cubical.Categories.Limits.IndexedProduct`:
   an X-indexed coproduct in C is an X-indexed product in C ^op, so the
   universal element, its notation, and all of its equations are
   obtained by transporting that module along ^op. Only the names and
   the direction of composition change.
-}
module Semantics.Structure.IndexedCoproduct where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.IndexedProduct.Base
open import Cubical.Categories.Presheaf.Representable

private
  variable
    ℓC ℓC' ℓ : Level

open Category

module _ (C : Category ℓC ℓC') where
  ΣTy : {X : Type ℓ} → (X → C .ob) → Type _
  ΣTy c⟨x⟩ = ΠTy (C ^op) c⟨x⟩

  IndexedCoproducts : (ℓ : Level) → Type _
  IndexedCoproducts ℓ = IndexedProducts (C ^op) ℓ

module ΣTyNotation {C : Category ℓC ℓC'} {X : Type ℓ}
  (c⟨x⟩ : X → C .ob) (Σue : ΣTy C {X = X} c⟨x⟩) where
  private
    module C = Category C
    module Π = ΠTyNotation {C = C ^op} c⟨x⟩ Σue

  open Π public using (vertex; element; universal)

  -- The coprojections are the "app"s of the opposite product.
  σ : ∀ x → C [ c⟨x⟩ x , vertex ]
  σ = Π.app

  -- Copairing is its "lda".
  elim : ∀ {Γ} → (∀ x → C [ c⟨x⟩ x , Γ ]) → C [ vertex , Γ ]
  elim = Π.lda

  ⊕β : ∀ {Γ} (f : ∀ x → C [ c⟨x⟩ x , Γ ]) (x : X)
     → σ x C.⋆ elim f ≡ f x
  ⊕β = Π.Πβ

  ⊕η : ∀ {Γ} (g : C [ vertex , Γ ]) → g ≡ elim (λ x → σ x C.⋆ g)
  ⊕η = Π.Πη

  -- The workhorse: maps out of a coproduct are determined componentwise.
  ⊕ext : ∀ {Γ} {g g' : C [ vertex , Γ ]}
       → (∀ x → σ x C.⋆ g ≡ σ x C.⋆ g') → g ≡ g'
  ⊕ext {g = g} {g' = g'} p = ⊕η g ∙ cong elim (funExt p) ∙ sym (⊕η g')

module IndexedCoproductsNotation {C : Category ℓC ℓC'} {ℓ}
  (Σs : IndexedCoproducts C ℓ) where
  private
    module Σ' {X : Type ℓ} c⟨x⟩ = ΣTyNotation {C = C} {X = X} c⟨x⟩ (Σs X c⟨x⟩)

  open Σ' public
  ⊕ᴰ : {X : Type ℓ} → (X → C .ob) → C .ob
  ⊕ᴰ = λ z → UniversalElement.vertex (Σs _ z)
