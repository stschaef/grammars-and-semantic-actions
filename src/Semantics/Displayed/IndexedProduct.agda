{-# OPTIONS --lossy-unification #-}
{- Displayed set-indexed products and coproducts.

   ccl builds displayed limits as `UniversalElementᴰ Cᴰ ue Pᴰ` for a
   displayed presheaf `Pᴰ`, and supplies the displayed presheaf via
   reusable combinators (`PshProdᴰ` for binary products). There is no
   indexed analogue, which is the one thing missing for a displayed
   version of `Semantics.Model`.

   Using the *uncurried* displayed presheaves — where
   `Presheafᴰ P Cᴰ ℓ` is literally `Presheaf (Cᴰ / P) ℓ` — the indexed
   analogue is short, and needs no `PathP` reasoning: reindex each
   `Pᴰ⟨x⟩` along the projection `ΠTyPsh P⟨x⟩ → P⟨x⟩ x` and take the
   *ordinary* indexed product of presheaves on `Cᴰ / ΠTyPsh P⟨x⟩`.
-}
module Semantics.Displayed.IndexedProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Instances.Sets using (_[-,_])
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.IndexedProduct
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Limits.IndexedProduct.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor.More using (Idᴰ)
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable

open import Semantics.Structure.IndexedCoproduct using (ΣTy)

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓ ℓP ℓPᴰ : Level

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  {X : Type ℓ} {P⟨x⟩ : X → Presheaf C ℓP}
  (Pᴰ⟨x⟩ : ∀ x → Presheafᴰ (P⟨x⟩ x) Cᴰ ℓPᴰ)
  where

  ΠTyPshᴰ : Presheafᴰ (ΠTyPsh P⟨x⟩) Cᴰ (ℓ-max ℓ ℓPᴰ)
  ΠTyPshᴰ =
    ΠTyPsh (λ x → Pᴰ⟨x⟩ x ∘F ((Idᴰ /Fᴰ appHet x) ^opF))
    where
    -- `PshHet Id P Q` is `PshHom P (reindPsh Id Q)`, and `reindPsh Id`
    -- is only isomorphic to the identity, not definitionally equal.
    appHet : ∀ x → PshHet Id (ΠTyPsh P⟨x⟩) (P⟨x⟩ x)
    appHet x =
      ΠTyPsh-app P⟨x⟩ x ⋆PshHom PshIso.trans (reindPshId≅ (P⟨x⟩ x))

------------------------------------------------------------------------
-- Displayed indexed products, and coproducts by ^op duality
------------------------------------------------------------------------

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  {X : Type ℓ} {c⟨x⟩ : X → Category.ob C}
  (c⟨x⟩ᴰ : ∀ x → Categoryᴰ.ob[_] Cᴰ (c⟨x⟩ x))
  where

  ΠTyᴰ : ΠTy C c⟨x⟩ → Type _
  ΠTyᴰ Π =
    UniversalElementᴰ Cᴰ
      (ΠTyPsh (λ x → C [-, c⟨x⟩ x ]))
      (ΠTyPshᴰ Cᴰ (λ x → Cᴰ [-][-, c⟨x⟩ᴰ x ]))
      Π


-- A displayed indexed coproduct is a displayed indexed product in the
-- opposite displayed category, exactly as `ΣTy` is `ΠTy` in the
-- opposite category.
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  {X : Type ℓ} {c⟨x⟩ : X → Category.ob C}
  (c⟨x⟩ᴰ : ∀ x → Categoryᴰ.ob[_] Cᴰ (c⟨x⟩ x))
  where
  ΣTyᴰ : ΣTy C c⟨x⟩ → Type _
  ΣTyᴰ = ΠTyᴰ (Cᴰ ^opᴰ) c⟨x⟩ᴰ
------------------------------------------------------------------------
-- Notation
------------------------------------------------------------------------

module ΠTyᴰNotation {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {X : Type ℓ} {c⟨x⟩ : X → Category.ob C}
  {c⟨x⟩ᴰ : ∀ x → Categoryᴰ.ob[_] Cᴰ (c⟨x⟩ x)}
  {Π : ΠTy C c⟨x⟩} (Πᴰ : ΠTyᴰ Cᴰ c⟨x⟩ᴰ Π)
  where
  open UniversalElementᴰNotation Cᴰ
    (ΠTyPsh (λ x → C [-, c⟨x⟩ x ]))
    (ΠTyPshᴰ Cᴰ (λ x → Cᴰ [-][-, c⟨x⟩ᴰ x ]))
    Πᴰ public

module ΣTyᴰNotation {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {X : Type ℓ} {c⟨x⟩ : X → Category.ob C}
  {c⟨x⟩ᴰ : ∀ x → Categoryᴰ.ob[_] Cᴰ (c⟨x⟩ x)}
  {Σ' : ΣTy C c⟨x⟩} (Σᴰ : ΣTyᴰ Cᴰ c⟨x⟩ᴰ Σ')
  where
  open ΠTyᴰNotation {Cᴰ = Cᴰ ^opᴰ} {c⟨x⟩ᴰ = c⟨x⟩ᴰ} Σᴰ public
