{-# OPTIONS --lossy-unification --allow-unsolved-metas #-}
{- The recursor, as an instance of the eliminator.

   Any model is a displayed model over the free one with constant
   fibres (`Semantics.Displayed.Weaken`), and a section of a weakening
   is exactly a functor. So the recursor is

       rec = introS⁻ (elim (weakenModel FreeModel M) ⟦lit⟧)

   rather than a second induction over `Exp`. This is ccl's pattern
   (`rec ı = introS⁻ (elim wkC ı)`), and it means the interpretation of
   the syntax cannot drift out of step with the eliminator.

   Note the consequence: `rec` now inherits the eight unfilled β/η
   holes in `Semantics.Free.Eliminator`, so it typechecks but is not
   yet a complete proof. The earlier standalone recursor was hole-free
   precisely because a plain `UniversalElement`'s β/η carry no `reind`;
   that duplication is what this replaces.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Semantics.Model

module Semantics.Free.Recursor {ℓ ℓ' ℓX} {Gen : hSet ℓX}
  (M : GrammarModel ℓ ℓ' ℓX Gen) where

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
import Cubical.Categories.Displayed.Instances.Weaken.Base as Wk

open import Semantics.Displayed.Model
open import Semantics.Displayed.Weaken
open import Semantics.Free.Syntax Gen
open import Semantics.Free.Model Gen
open import Semantics.Free.Eliminator Gen

private
  module M = GrammarModel M

  -- M, viewed as a displayed model over the syntax.
  Mᴰ : Modelᴰ FreeModel ℓ ℓ'
  Mᴰ = weakenModel FreeModel M.model

  ı : Interpᴰ Mᴰ
  ı = M.⟦lit⟧

-- | The interpretation of the syntax in M.
rec : Functor FREE (Model.C M.model)
rec = Wk.introS⁻ (elim Mᴰ ı)

recOb : Ty → Category.ob (Model.C M.model)
recOb = Functor.F-ob rec

recHom : ∀ {A B} → Exp A B → Model.C M.model [ recOb A , recOb B ]
recHom = Functor.F-hom rec
