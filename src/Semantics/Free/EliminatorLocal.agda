{-# OPTIONS --lossy-unification #-}
{- The *local* eliminator out of the free model.

   `Semantics.Free.Eliminator.elim` asks for a `Modelᴰ FreeModel`:
   displayed indexed (co)products *over the free model's own* `Πs`/`Σs`.
   Stating those directly is painful, because each factor `Aᴰ x` lives
   over a different base object `A x` and the universal property is
   heterogeneous.

   A caller proving a metatheorem does not want to write that. What
   they have is fibrewise data — for canonicity, a family of predicates
   over a *fixed* grammar, closed under Σ and Π of predicates — plus
   the ability to substitute along a morphism of the syntax. That is
   exactly `Modelⱽ`, and `Modelⱽ→Modelᴰ` bridges the two: the
   (co)cartesian lifts move the fibrewise product onto the base one.

   So `elimLocal` is the eliminator a metatheorem should call. The
   heterogeneous bookkeeping stays here.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Free.EliminatorLocal {ℓ} (Gen : hSet ℓ) where

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base

open import Semantics.Displayed.Model
open import Semantics.Displayed.ModelV
open import Semantics.Free.Model Gen
open import Semantics.Free.Eliminator Gen

module _ {ℓCᴰ ℓCᴰ'} (Mⱽ : Modelⱽ FreeModel ℓCᴰ ℓCᴰ') where
  private
    module Mⱽ = Modelⱽ Mⱽ

    Mᴰ : Modelᴰ FreeModel ℓCᴰ ℓCᴰ'
    Mᴰ = Modelⱽ→Modelᴰ Mⱽ

  -- | The generators still have to be interpreted, but only by
  --   displayed objects — no universal properties.
  Interpⱽ : Type _
  Interpⱽ = Interpᴰ Mᴰ

  -- | The local eliminator: fibrewise structure in, a global section
  --   of the displayed category out.
  elimLocal : Interpⱽ → GlobalSection Mⱽ.Cᴰ
  elimLocal = elim Mᴰ
