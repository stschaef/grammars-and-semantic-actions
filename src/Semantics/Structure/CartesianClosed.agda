{-# OPTIONS --lossy-unification #-}
{- Cartesian closure, as a mixin on a model.

   `Semantics.Model` asks for a *monoidal* biclosure — ⊸ and ⟜, the
   two slot-closures of ⊗. That is separate from closure of the
   cartesian product `&`, which is what `Grammar.Function`'s `⇒`
   is, and which `Grammar.Later` and `Grammar.Distributivity` use.

   This is a mixin rather than a field of `Model` for the same
   reason `HasInitialAlgebras` and `LaterStr` are: not every
   biclosed monoidal category is cartesian closed, and the models
   that are can say so separately.

   `&` here is the binary case of the model's set-indexed product,
   so `⇒` is the right adjoint of `- & A`.
-}
module Semantics.Structure.CartesianClosed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool using (Bool; true; false; isSetBool)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Limits.IndexedProduct.Base

open import Semantics.Model

private
  variable
    ℓ ℓ' ℓX : Level

open Functor

module _ (M : Model ℓ ℓ' ℓX) where
  open Model M
  private
    module C = Category C

  -- The two-element index set, as in `Semantics.Notation`.
  Two : hSet ℓX
  Two = Lift ℓX Bool , isOfHLevelLift 2 isSetBool

  pair : C.ob → C.ob → ⟨ Two ⟩ → C.ob
  pair A B (lift true) = A
  pair A B (lift false) = B

  private
    module Prod (A B : C.ob) = ΠTyNotation (pair A B) (Πs Two (pair A B))

  infixr 6 _&M_
  _&M_ : C.ob → C.ob → C.ob
  A &M B = Prod.vertex A B

  -- | Product with a fixed object, as an endofunctor.
  prodR : C.ob → Functor C C
  prodR A .F-ob X = X &M A
  prodR A .F-hom {X} {Y} f = Prod.lda Y A λ where
    (lift true) → Prod.app X A (lift true) C.⋆ f
    (lift false) → Prod.app X A (lift false)
  prodR A .F-id {X} = Prod.extensionality X A (funExt λ where
    (lift true) →
      Prod.Πβ X A _ (lift true) ∙ C.⋆IdR _ ∙ sym (C.⋆IdL _)
    (lift false) →
      Prod.Πβ X A _ (lift false) ∙ sym (C.⋆IdL _))
  prodR A .F-seq {X} {Y} {Z} f g =
    Prod.extensionality Z A (funExt λ where
      (lift true) →
        Prod.Πβ Z A _ (lift true)
        ∙ sym (C.⋆Assoc _ _ _
               ∙ cong (prodR A .F-hom f C.⋆_) (Prod.Πβ Z A _ (lift true))
               ∙ sym (C.⋆Assoc _ _ _)
               ∙ cong (C._⋆ g) (Prod.Πβ Y A _ (lift true))
               ∙ C.⋆Assoc _ _ _)
      (lift false) →
        Prod.Πβ Z A _ (lift false)
        ∙ sym (C.⋆Assoc _ _ _
               ∙ cong (prodR A .F-hom f C.⋆_) (Prod.Πβ Z A _ (lift false))
               ∙ Prod.Πβ Y A _ (lift false)))
  -- | `A ⇒ B` is the right adjoint of `- & A` at `B`.
  ⇒At : C.ob → C.ob → Type (ℓ-max ℓ ℓ')
  ⇒At A B = RightAdjointAt (prodR A) B

  record CartesianClosed : Type (ℓ-max ℓ ℓ') where
    field
      ⇒ues : ∀ A B → ⇒At A B

    module ⇒ue {A B} = UniversalElementNotation (⇒ues A B)

    infixr 3 _⇒_
    _⇒_ : C.ob → C.ob → C.ob
    A ⇒ B = ⇒ue.vertex {A} {B}

    ⇒-app : ∀ {A B} → C [ (A ⇒ B) &M A , B ]
    ⇒-app = ⇒ue.element

    ⇒-intro : ∀ {A B D} → C [ D &M A , B ] → C [ D , A ⇒ B ]
    ⇒-intro = ⇒ue.intro

    ⇒-β : ∀ {A B D} {f : C [ D &M A , B ]}
        → prodR A .F-hom (⇒-intro f) C.⋆ ⇒-app ≡ f
    ⇒-β = ⇒ue.β

    ⇒-η : ∀ {A B D} {g : C [ D , A ⇒ B ]}
        → g ≡ ⇒-intro (prodR A .F-hom g C.⋆ ⇒-app)
    ⇒-η = ⇒ue.η
