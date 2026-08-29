{-# OPTIONS --lossy-unification #-}
{- The families model carries a later modality.

   `Grammar.Later` defines ▷ A as "A, after consuming any nonempty
   prefix" and proves Löb induction for it by well-founded recursion on
   string length. That is exactly the data `Semantics.Later.LaterStr`
   asks for, once ▷ is packaged as an endofunctor of the model.

   With this, `▷e` may be used in the functor codes of
   `Semantics.Inductive.Functor`, so guarded definitions are expressible
   over real grammars.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Instances.FamiliesLater (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure using (⟨_⟩)

import Cubical.Categories.Functor as CF

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet hiding (⟨_⟩)
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.Function.AsPrimitive.Base Alphabet
open import Grammar.Product.Base Alphabet
open import Grammar.Product.Properties Alphabet
open import Grammar.String.Base Alphabet
open import Grammar.Top.Base Alphabet
open import Grammar.Derivative.String Alphabet
open import Grammar.Later.Base Alphabet
open import Term.Base Alphabet

import Semantics.Later
import Semantics.Notation

open import Semantics.Instances.Families Alphabet

open CF.Functor

private
  variable
    ℓA ℓB ℓC : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC

------------------------------------------------------------------------
-- ▷ is a set-valued endofunctor
------------------------------------------------------------------------

opaque
  unfolding _⇒_
  isSetGrammar⇒ : isSetGrammar B → isSetGrammar (A ⇒ B)
  isSetGrammar⇒ isSetB w = isSetΠ λ _ → isSetB w

isSetGrammar▷ : isSetGrammar A → isSetGrammar (▷ A)
isSetGrammar▷ isSetA =
  isSetGrammar&ᴰ λ w →
    isSetGrammar⇒
      (isSetGrammar⊗ (isLang→isSetGrammar (isLang⌈⌉ (w .fst))) isSetA)

⇒-mapCod : A ⊢ B → (C ⇒ A) ⊢ (C ⇒ B)
⇒-mapCod f = ⇒-intro (f ∘g ⇒-app)

▷map : A ⊢ B → ▷ A ⊢ ▷ B
▷map f = &ᴰ-intro λ w → ⇒-mapCod (id ,⊗ f) ∘g π w

opaque
  unfolding _⇒_ ⇒-intro ⇒-app _⊗_ ⊗-intro
  ▷map-id : ▷map (id {A = A}) ≡ id
  ▷map-id = refl

  ▷map-seq : (f : A ⊢ B) (g : B ⊢ C) → ▷map (g ∘g f) ≡ ▷map g ∘g ▷map f
  ▷map-seq f g = refl

------------------------------------------------------------------------
-- Packaging it as a `LaterStr`
------------------------------------------------------------------------

module _ (ℓ : Level) (Gen : hSet ℓ) (lit : ⟨ Gen ⟩ → SetGrammar ℓ) where
  private
    M = FamiliesOn ℓ Gen lit

  module N = Semantics.Notation M
  module SemL = Semantics.Later M

  ▷Endo : CF.Functor N.C N.C
  ▷Endo .F-ob A = ▷ (A .fst) , isSetGrammar▷ (A .snd)
  ▷Endo .F-hom = ▷map
  ▷Endo .F-id = ▷map-id
  ▷Endo .F-seq f g = ▷map-seq f g

  FamiliesLater : SemL.LaterStr
  FamiliesLater .SemL.LaterStr.▷F = ▷Endo
  -- The model's ⊤ is the empty indexed product, so it maps into the
  -- library's ⊤ by its universal property.
  FamiliesLater .SemL.LaterStr.lob f = lob f ∘g ⊤-intro
