{-# OPTIONS --lossy-unification #-}
{- A model of the grammar DSL.

   The Lambekᴰ connectives are interpreted in *any* category carrying
   the following universal structure:

     - a monoidal structure, interpreting ⊗ and ε.  This is the
       structure demanded by the theory of monoids: strings are the
       free monoid on the alphabet and sequencing is its
       multiplication, but nothing below depends on that;
     - a biclosure of that monoidal structure, interpreting ⊸ and ⟜;
     - set-indexed products and coproducts, interpreting &ᴰ and ⊕ᴰ.
       The nullary and binary connectives ⊤, ⊥, & and ⊕ are *derived*
       from these rather than postulated;
     - an interpretation of each generator (each alphabet character) as
       an object, interpreting the literals.

   Indices are h-sets rather than arbitrary types. That is what the
   families model supports: a `Category` in the sense of `cubical` has
   hom-sets, so its objects are the set-valued grammars, and a
   coproduct of set-valued grammars indexed by a non-set would not be
   set-valued.

   Nothing here mentions families of sets over strings; that is one
   model among others (see `Semantics.Instances.Families`).
-}
module Semantics.Model where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Limits.IndexedProduct.Base

open import Semantics.Structure.Biclosed
open import Semantics.Structure.IndexedCoproduct

private
  variable
    ℓ ℓ' ℓX : Level

module _ (C : Category ℓ ℓ') where
  -- The h-set-indexed restrictions of ccl's `IndexedProducts` and of
  -- its dual from `Semantics.Structure.IndexedCoproduct`.
  SetIndexedProducts : (ℓX : Level) → Type _
  SetIndexedProducts ℓX =
    (X : hSet ℓX) (A : ⟨ X ⟩ → Category.ob C) → ΠTy C A

  SetIndexedCoproducts : (ℓX : Level) → Type _
  SetIndexedCoproducts ℓX =
    (X : hSet ℓX) (A : ⟨ X ⟩ → Category.ob C) → ΣTy C A

-- | The linear-logical structure, with no choice of generators yet.
record Model (ℓ ℓ' ℓX : Level)
  : Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' ℓX))) where
  field
    MC : MonoidalCategory ℓ ℓ'

  open MonoidalCategory MC public using (C)

  field
    biclosed : Biclosed MC
    Πs : SetIndexedProducts C ℓX
    Σs : SetIndexedCoproducts C ℓX

-- | A model together with an interpretation of the alphabet.
record GrammarModel (ℓ ℓ' ℓX : Level) (Gen : hSet ℓX)
  : Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' ℓX))) where
  field
    model : Model ℓ ℓ' ℓX

  open Model model public

  field
    ⟦lit⟧ : ⟨ Gen ⟩ → MonoidalCategory.ob MC
