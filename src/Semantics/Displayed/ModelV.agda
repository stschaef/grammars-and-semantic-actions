{-# OPTIONS --lossy-unification #-}
{- Vertical displayed models.

   `Modelᴰ M` asks for displayed structure over *M's own* universal
   elements. `Modelⱽ M` asks for it fibrewise, over the identity —
   which is what survives reindexing along an arbitrary functor,
   and hence what a caller of `elimLocal` should supply.

   It is necessarily a hybrid. The limit part verticalises: an
   indexed product of displayed objects over a common base is again
   over that base. The *tensor* does not — `x ⊗ y` is a different
   base object from either factor, so there is no fibrewise version
   and the monoidal part stays displayed over M's, to be reindexed
   along a monoidal functor. That asymmetry is why ccl reindexes
   `CartesianCategoryⱽ` along any functor but `MonoidalCategoryᴰ`
   only along a monoidal one.

   `cartesianLifts` is what lets the displayed-over-the-base
   structure be recovered from the fibrewise one.
-}
module Semantics.Displayed.ModelV where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
  using (isFibration; CartesianLift)
open import Cubical.Categories.Presheaf.Representable using (UniversalElement)
open import Cubical.Categories.Displayed.Monoidal.Base

open import Semantics.Model
open import Semantics.Displayed.Model
open import Semantics.Displayed.IndexedProductV

private
  variable
    ℓ ℓ' ℓX ℓCᴰ ℓCᴰ' : Level

record Modelⱽ (M : Model ℓ ℓ' ℓX) (ℓCᴰ ℓCᴰ' : Level)
  : Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓX (ℓ-max ℓCᴰ ℓCᴰ')))) where
  private module M = Model M
  field
    Cᴰ : Categoryᴰ M.C ℓCᴰ ℓCᴰ'

  private module Cᴰ = Categoryᴰ Cᴰ

  field
    -- Monoidal: displayed over M's, since ⊗ has no fibrewise form.
    MCᴰ : MonoidalStrᴰ M.MC Cᴰ
    biclosedᴰ : Biclosedᴰ M.MC MCᴰ M.biclosed

    -- Limits: fibrewise.
    Πsⱽ : {c : Category.ob M.C} (X : hSet ℓX)
          (Aⱽ : ⟨ X ⟩ → Cᴰ.ob[ c ]) → ΠTyⱽ Cᴰ Aⱽ
    Σsⱽ : {c : Category.ob M.C} (X : hSet ℓX)
          (Aⱽ : ⟨ X ⟩ → Cᴰ.ob[ c ]) → ΣTyⱽ Cᴰ Aⱽ

    -- What recovers the displayed structure from the fibrewise one:
    -- indexed products are pulled back along the projections, and
    -- indexed coproducts pushed forward along the injections.
    cartesianLifts : isFibration Cᴰ
    cocartesianLifts : isFibration (Cᴰ ^opᴰ)

------------------------------------------------------------------------
-- Verticalisation is enough: a `Modelⱽ` is a `Modelᴰ`
--
-- The monoidal half is already displayed over M's and carries over
-- unchanged. The limit half is fibrewise, and `ΠTyⱽ+π*→ᴰ` /
-- `ΣTyⱽ+π*→ᴰ` move it onto M's own indexed (co)products using the
-- (co)cartesian lifts.
------------------------------------------------------------------------

module _ {M : Model ℓ ℓ' ℓX} (Mⱽ : Modelⱽ M ℓCᴰ ℓCᴰ') where
  private
    module M = Model M
    module Mⱽ = Modelⱽ Mⱽ
  open UniversalElement
  open Modelᴰ

  Modelⱽ→Modelᴰ : Modelᴰ M ℓCᴰ ℓCᴰ'
  Modelⱽ→Modelᴰ .Cᴰ = Mⱽ.Cᴰ
  Modelⱽ→Modelᴰ .MCᴰ = Mⱽ.MCᴰ
  Modelⱽ→Modelᴰ .biclosedᴰ = Mⱽ.biclosedᴰ
  Modelⱽ→Modelᴰ .Πsᴰ X A Aᴰ =
    ΠTyⱽ+π*→ᴰ Mⱽ.Cᴰ (M.Πs X A) Aᴰ π*Aᴰ (Mⱽ.Πsⱽ X (λ x → π*Aᴰ x .fst))
    where
    π*Aᴰ : ∀ x → CartesianLift Mⱽ.Cᴰ (M.Πs X A .element x) (Aᴰ x)
    π*Aᴰ x = Mⱽ.cartesianLifts (Aᴰ x) _ (M.Πs X A .element x)
  Modelⱽ→Modelᴰ .Σsᴰ X A Aᴰ =
    ΣTyⱽ+π*→ᴰ Mⱽ.Cᴰ (M.Σs X A) Aᴰ σ*Aᴰ (Mⱽ.Σsⱽ X (λ x → σ*Aᴰ x .fst))
    where
    σ*Aᴰ : ∀ x → CartesianLift (Mⱽ.Cᴰ ^opᴰ) (M.Σs X A .element x) (Aᴰ x)
    σ*Aᴰ x = Mⱽ.cocartesianLifts (Aᴰ x) _ (M.Σs X A .element x)
