{-# OPTIONS --lossy-unification #-}
{- Vertical set-indexed products and coproducts.

   `Presheafⱽ x Cᴰ` is `Presheafᴰ (C [-, x ]) Cᴰ`, i.e. a presheaf
   on `Cᴰ / (C [-, x ])`. For a *fixed* base object all components
   of an indexed family live on that same category, so unlike the
   displayed case (`Semantics.Displayed.IndexedProduct`) there is
   nothing to reindex: the vertical indexed product is ccl's
   ordinary `ΠTyPsh`, unchanged.

   Vertical is the notion that survives reindexing along an
   arbitrary functor, which is what `elimLocal` needs — see
   ccl's `Displayed/Limits/{Terminal,BinProduct}` for the terminal
   and binary cases this generalises.
-}
module Semantics.Displayed.IndexedProductV where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets using (_[-,_])
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.IndexedProduct
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓ ℓPᴰ : Level

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  {c : Category.ob C} where

  -- | The vertical indexed product of displayed presheaves. All
  --   components are presheaves on the same category, so this is
  --   just the ordinary one.
  ΠTyPshⱽ : {X : Type ℓ} → (X → Presheafⱽ c Cᴰ ℓPᴰ)
          → Presheafⱽ c Cᴰ (ℓ-max ℓ ℓPᴰ)
  ΠTyPshⱽ = ΠTyPsh

  -- | A vertical set-indexed product: fibrewise, over the identity.
  ΠTyⱽ : {X : Type ℓ} (Aⱽ : X → Categoryᴰ.ob[_] Cᴰ c) → Type _
  ΠTyⱽ Aⱽ =
    UniversalElementⱽ' Cᴰ c (ΠTyPshⱽ (λ x → Cᴰ [-][-, Aⱽ x ]))

-- | Vertical coproducts are the ^op dual, as in the displayed case.
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  {c : Category.ob C} where

  ΣTyⱽ : {X : Type ℓ} (Aⱽ : X → Categoryᴰ.ob[_] Cᴰ c) → Type _
  ΣTyⱽ = ΠTyⱽ (Cᴰ ^opᴰ) {c}
