{-# OPTIONS --lossy-unification #-}
{- Displayed right adjoints, in the uncurried style.

   ccl has `RightAdjointAtᴰ` in `Displayed/Adjoint/More`, but it is
   built on the *curried* displayed presheaves. `Semantics.Model`'s
   biclosure is a pair of `RightAdjointAt`s, so a displayed model needs
   the uncurried counterpart to sit alongside the uncurried displayed
   indexed (co)products.

   The construction is short for the same reason as `ΠTyPshᴰ`: a
   displayed presheaf over `P` is a plain presheaf on `Cᴰ / P`, so
   reindexing is precomposition with a functor, and `_/Fᴰ_` supplies
   that functor. Here the presheaf morphism it needs is the identity,
   since `RightAdjointProf F ⟅ d ⟆` is by definition
   `reindPsh F (D [-, d ])`.
-}
module Semantics.Displayed.RightAdjoint where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Instances.Sets using (_[-,_])
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.Reindex

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {F : Functor C D}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  where

  -- The displayed presheaf whose fibre over `f : D [ F Γ , d ]` is
  -- `Dᴰ [ f ][ Fᴰ Γᴰ , dᴰ ]`.
  RightAdjointProfᴰ : {d : Category.ob D} (dᴰ : Categoryᴰ.ob[_] Dᴰ d)
    → Presheafᴰ (RightAdjointProf F ⟅ d ⟆) Cᴰ ℓDᴰ'
  RightAdjointProfᴰ dᴰ =
    (Dᴰ [-][-, dᴰ ]) ∘F ((Fᴰ /Fᴰ idPshHom) ^opF)

  RightAdjointAtᴰ : {d : Category.ob D}
    → RightAdjointAt F d → Categoryᴰ.ob[_] Dᴰ d → Type _
  RightAdjointAtᴰ {d = d} R⟅d⟆ dᴰ =
    UniversalElementᴰ Cᴰ
      (RightAdjointProf F ⟅ d ⟆)
      (RightAdjointProfᴰ dᴰ)
      R⟅d⟆

module RightAdjointAtᴰNotation {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {F : Functor C D}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {Fᴰ : Functorᴰ F Cᴰ Dᴰ} {d : Category.ob D}
  {R⟅d⟆ : RightAdjointAt F d} {dᴰ : Categoryᴰ.ob[_] Dᴰ d}
  (Rᴰ : RightAdjointAtᴰ Fᴰ R⟅d⟆ dᴰ)
  where
  open UniversalElementᴰNotation Cᴰ
    (RightAdjointProf F ⟅ d ⟆)
    (RightAdjointProfᴰ Fᴰ dᴰ)
    Rᴰ public
