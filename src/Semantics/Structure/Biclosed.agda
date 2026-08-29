{-# OPTIONS --lossy-unification #-}
{- Biclosure of a monoidal category, as universal elements.

   `B ⊸ D` is the right adjoint of `- ⊗ B` at D and `D ⟜ A` is the
   right adjoint of `A ⊗ -` at D, so that (cf. `Grammar.LinearFunction`)

       A ⊗ B ⊢ D   ≃   A ⊢ B ⊸ D
       A ⊗ B ⊢ D   ≃   B ⊢ D ⟜ A

   Both are `RightAdjointAt` of the two partial applications of the
   tensor, so `intro`/`element`/`β`/`η` come from
   `UniversalElementNotation`; the definitions below only restate them
   with the names used by the grammar DSL.
-}
module Semantics.Structure.Biclosed where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More

private
  variable
    ℓ ℓ' : Level

module _ (M : MonoidalCategory ℓ ℓ') where
  open MonoidalCategory M

  -- Tensoring on the right by B, and on the left by A.
  tensorR : ob → Functor C C
  tensorR B = ─⊗─ ∘F linj C C B

  tensorL : ob → Functor C C
  tensorL A = ─⊗─ ∘F rinj C C A

  ⊸At : (B D : ob) → Type (ℓ-max ℓ ℓ')
  ⊸At B D = RightAdjointAt (tensorR B) D

  ⟜At : (A D : ob) → Type (ℓ-max ℓ ℓ')
  ⟜At A D = RightAdjointAt (tensorL A) D

  record Biclosed : Type (ℓ-max ℓ ℓ') where
    field
      ⊸ues : ∀ B D → ⊸At B D
      ⟜ues : ∀ A D → ⟜At A D

    module ⊸ue {B D} = UniversalElementNotation (⊸ues B D)
    module ⟜ue {A D} = UniversalElementNotation (⟜ues A D)

    infixr 2 _⊸_
    infixl 2 _⟜_

    _⊸_ : ob → ob → ob
    B ⊸ D = ⊸ue.vertex {B} {D}

    _⟜_ : ob → ob → ob
    D ⟜ A = ⟜ue.vertex {A} {D}

    ------------------------------------------------------------------
    -- ⊸
    ------------------------------------------------------------------
    ⊸-app : ∀ {B D} → Hom[ (B ⊸ D) ⊗ B , D ]
    ⊸-app = ⊸ue.element

    ⊸-intro : ∀ {A B D} → Hom[ A ⊗ B , D ] → Hom[ A , B ⊸ D ]
    ⊸-intro = ⊸ue.intro

    ⊸-β : ∀ {A B D} {f : Hom[ A ⊗ B , D ]}
        → (⊸-intro f ⊗ₕ id) ⋆ ⊸-app ≡ f
    ⊸-β = ⊸ue.β

    ⊸-η : ∀ {A B D} {g : Hom[ A , B ⊸ D ]}
        → g ≡ ⊸-intro ((g ⊗ₕ id) ⋆ ⊸-app)
    ⊸-η = ⊸ue.η

    ⊸-ext : ∀ {A B D} {g g' : Hom[ A , B ⊸ D ]}
          → (g ⊗ₕ id) ⋆ ⊸-app ≡ (g' ⊗ₕ id) ⋆ ⊸-app → g ≡ g'
    ⊸-ext = ⊸ue.extensionality

    ------------------------------------------------------------------
    -- ⟜
    ------------------------------------------------------------------
    ⟜-app : ∀ {A D} → Hom[ A ⊗ (D ⟜ A) , D ]
    ⟜-app = ⟜ue.element

    ⟜-intro : ∀ {A B D} → Hom[ A ⊗ B , D ] → Hom[ B , D ⟜ A ]
    ⟜-intro = ⟜ue.intro

    ⟜-β : ∀ {A B D} {f : Hom[ A ⊗ B , D ]}
        → (id ⊗ₕ ⟜-intro f) ⋆ ⟜-app ≡ f
    ⟜-β = ⟜ue.β

    ⟜-η : ∀ {A B D} {g : Hom[ B , D ⟜ A ]}
        → g ≡ ⟜-intro ((id ⊗ₕ g) ⋆ ⟜-app)
    ⟜-η = ⟜ue.η

    ⟜-ext : ∀ {A B D} {g g' : Hom[ B , D ⟜ A ]}
          → (id ⊗ₕ g) ⋆ ⟜-app ≡ (id ⊗ₕ g') ⋆ ⟜-app → g ≡ g'
    ⟜-ext = ⟜ue.extensionality

    ------------------------------------------------------------------
    -- Naturality of the transposes, inherited from the universal
    -- element. These are what let one reason about maps out of a
    -- tensor componentwise.
    ------------------------------------------------------------------
    ⊸-intro-natural : ∀ {A A' B D} {f : Hom[ A' , A ]} {p : Hom[ A ⊗ B , D ]}
      → f ⋆ ⊸-intro p ≡ ⊸-intro ((f ⊗ₕ id) ⋆ p)
    ⊸-intro-natural = ⊸ue.intro-natural

    ⟜-intro-natural : ∀ {A B B' D} {f : Hom[ B' , B ]} {p : Hom[ A ⊗ B , D ]}
      → f ⋆ ⟜-intro p ≡ ⟜-intro ((id ⊗ₕ f) ⋆ p)
    ⟜-intro-natural = ⟜ue.intro-natural
