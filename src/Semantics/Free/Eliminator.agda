{-# OPTIONS --lossy-unification #-}
{- The eliminator out of the free model.

   A displayed model over `FreeModel`, together with an interpretation
   of the generators, determines a section of it. This is the shape a
   gluing metatheorem takes: choose a displayed model, interpret the
   generators, and the eliminator gives the property for every object
   and every morphism of the syntax.

   The object part is below. It already pins down that `Modelᴰ` carries
   the right data: each type former is interpreted by the *vertex* of
   the corresponding displayed universal element.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Semantics.Free.Eliminator {ℓ} (Gen : hSet ℓ) where

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Monoidal.Base

open import Semantics.Model
open import Semantics.Displayed.Model
open import Semantics.Free.Syntax Gen
open import Semantics.Free.Model Gen

module _ {ℓCᴰ ℓCᴰ'} (Mᴰ : Modelᴰ FreeModel ℓCᴰ ℓCᴰ') where

  open Modelᴰ Mᴰ

  private
    module Cᴰ = Categoryᴰ Cᴰ

  open MonoidalStrᴰ MCᴰ
  open Biclosedᴰ biclosedᴰ

  -- | An interpretation of the generators.
  Interpᴰ : Type (ℓ-max ℓ ℓCᴰ)
  Interpᴰ = ∀ g → Cᴰ.ob[ ↑ g ]

  module _ (ı : Interpᴰ) where
    elimOb : ∀ A → Cᴰ.ob[ A ]
    elimOb (↑ g) = ı g
    elimOb εT = unitᴰ
    elimOb (A ⊗T B) = elimOb A ⊗ᴰ elimOb B
    elimOb (A ⊸T B) = ⊸uesᴰ (elimOb A) (elimOb B) .fst
    elimOb (A ⟜T B) = ⟜uesᴰ (elimOb B) (elimOb A) .fst
    elimOb (⊕T X A) = Σsᴰ X A (λ x → elimOb (A x)) .fst
    elimOb (&T X A) = Πsᴰ X A (λ x → elimOb (A x)) .fst
