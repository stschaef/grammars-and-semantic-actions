{-# OPTIONS --lossy-unification #-}
{- Displayed models.

   A displayed model over `M` is a displayed category over `M`'s
   underlying category carrying displayed versions of everything
   `Semantics.Model.Model` asks for: a displayed monoidal structure,
   displayed right adjoints for the two slot functors of the tensor,
   and displayed set-indexed products and coproducts.

   This is what a gluing/logical-relations argument is stated against:
   a metatheorem about the free model is a section of a displayed model
   over it.
-}
module Semantics.Displayed.Model where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Monoidal.Base
open import Cubical.Categories.Displayed.Instances.BinProduct.More

open import Semantics.Model
open import Semantics.Structure.Biclosed
open import Semantics.Structure.IndexedCoproduct
open import Semantics.Displayed.IndexedProduct
open import Semantics.Displayed.RightAdjoint

private
  variable
    ℓ ℓ' ℓX ℓCᴰ ℓCᴰ' : Level

------------------------------------------------------------------------
-- Displayed biclosure
------------------------------------------------------------------------

module _ (M : MonoidalCategory ℓ ℓ')
  {Cᴰ : Categoryᴰ (MonoidalCategory.C M) ℓCᴰ ℓCᴰ'}
  (Mᴰ : MonoidalStrᴰ M Cᴰ)
  where
  private
    module M = MonoidalCategory M
    module Cᴰ = Categoryᴰ Cᴰ
  open MonoidalStrᴰ Mᴰ

  -- The displayed slot functors: tensoring on the right by Bᴰ, and on
  -- the left by Aᴰ.
  tensorRᴰ : {B : M.ob} → Cᴰ.ob[ B ] → Functorᴰ (tensorR M B) Cᴰ Cᴰ
  tensorRᴰ Bᴰ = ─⊗ᴰ─ ∘Fᴰ linjᴰ Cᴰ Cᴰ Bᴰ

  tensorLᴰ : {A : M.ob} → Cᴰ.ob[ A ] → Functorᴰ (tensorL M A) Cᴰ Cᴰ
  tensorLᴰ Aᴰ = ─⊗ᴰ─ ∘Fᴰ rinjᴰ Cᴰ Cᴰ Aᴰ

  ⊸Atᴰ : {B D : M.ob} → Cᴰ.ob[ B ] → Cᴰ.ob[ D ] → ⊸At M B D → Type _
  ⊸Atᴰ Bᴰ Dᴰ ue = RightAdjointAtᴰ (tensorRᴰ Bᴰ) ue Dᴰ

  ⟜Atᴰ : {A D : M.ob} → Cᴰ.ob[ A ] → Cᴰ.ob[ D ] → ⟜At M A D → Type _
  ⟜Atᴰ Aᴰ Dᴰ ue = RightAdjointAtᴰ (tensorLᴰ Aᴰ) ue Dᴰ

  record Biclosedᴰ (bc : Biclosed M) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓCᴰ ℓCᴰ')) where
    private module bc = Biclosed bc
    field
      ⊸uesᴰ : {B D : M.ob} (Bᴰ : Cᴰ.ob[ B ]) (Dᴰ : Cᴰ.ob[ D ])
            → ⊸Atᴰ Bᴰ Dᴰ (bc.⊸ues B D)
      ⟜uesᴰ : {A D : M.ob} (Aᴰ : Cᴰ.ob[ A ]) (Dᴰ : Cᴰ.ob[ D ])
            → ⟜Atᴰ Aᴰ Dᴰ (bc.⟜ues A D)

------------------------------------------------------------------------
-- Displayed models
------------------------------------------------------------------------

record Modelᴰ (M : Model ℓ ℓ' ℓX) (ℓCᴰ ℓCᴰ' : Level)
  : Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓX (ℓ-max ℓCᴰ ℓCᴰ')))) where
  private module M = Model M
  field
    Cᴰ : Categoryᴰ M.C ℓCᴰ ℓCᴰ'

  private module Cᴰ = Categoryᴰ Cᴰ

  field
    MCᴰ : MonoidalStrᴰ M.MC Cᴰ
    biclosedᴰ : Biclosedᴰ M.MC MCᴰ M.biclosed
    Πsᴰ : (X : hSet ℓX) (A : ⟨ X ⟩ → Category.ob M.C)
          (Aᴰ : ∀ x → Cᴰ.ob[ A x ])
        → ΠTyᴰ Cᴰ Aᴰ (M.Πs X A)
    Σsᴰ : (X : hSet ℓX) (A : ⟨ X ⟩ → Category.ob M.C)
          (Aᴰ : ∀ x → Cᴰ.ob[ A x ])
        → ΣTyᴰ Cᴰ Aᴰ (M.Σs X A)
