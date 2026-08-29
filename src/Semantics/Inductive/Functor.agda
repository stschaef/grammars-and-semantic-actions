{-# OPTIONS --lossy-unification #-}
{- Syntax for strictly positive endofunctors on a model.

   `Functor X` is a code for a strictly positive functor in the
   variables X (X indexes a family of mutually inductive definitions).
   `⟦ F ⟧ : (X → Grammar) → Grammar` interprets a code and `map` gives
   its functorial action.

   Two differences from `Grammar.Inductive.Functor`:

     - there are no `LiftG`s. A model has a single level of objects, so
       codes and their interpretations live at that level;

     - there is a code `∘e` for postcomposing with *any* endofunctor of
       the model. Strict positivity is preserved because an endofunctor
       is covariant by definition. This is what makes guarded recursion
       expressible: `▷e F = ∘e ▷ F` (see `Semantics.Later`).
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Semantics.Model

module Semantics.Inductive.Functor {ℓ ℓ' ℓX} {Gen : hSet ℓX}
  (M : GrammarModel ℓ ℓ' ℓX Gen) where

import Cubical.Categories.Functor as CF

open import Semantics.Notation M
open CF.Functor

private
  variable
    X : Type ℓX

-- | Endofunctors of the model, i.e. the modalities available for use
--   in a strictly positive position.
Endo : Type (ℓ-max ℓ ℓ')
Endo = CF.Functor C C

data Functor (X : Type ℓX) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓX)) where
  k : Grammar → Functor X
  Var : X → Functor X
  &e : (Y : hSet ℓX) → (⟨ Y ⟩ → Functor X) → Functor X
  ⊕e : (Y : hSet ℓX) → (⟨ Y ⟩ → Functor X) → Functor X
  _⊗e_ : Functor X → Functor X → Functor X
  ∘e : Endo → Functor X → Functor X

infixr 25 _⊗e_

⟦_⟧ : Functor X → (X → Grammar) → Grammar
⟦ k A ⟧ _ = A
⟦ Var x ⟧ A = A x
⟦ &e Y F ⟧ A = &[ y ∈ Y ] ⟦ F y ⟧ A
⟦ ⊕e Y F ⟧ A = ⊕[ y ∈ Y ] ⟦ F y ⟧ A
⟦ F ⊗e F' ⟧ A = ⟦ F ⟧ A ⊗ ⟦ F' ⟧ A
⟦ ∘e E F ⟧ A = E .F-ob (⟦ F ⟧ A)

module _ {X : Type ℓX} where
  map : (F : Functor X) {A B : X → Grammar}
      → (∀ x → A x ⊢ B x) → ⟦ F ⟧ A ⊢ ⟦ F ⟧ B
  map (k A) f = id
  map (Var x) f = f x
  map (&e Y F) f = &ᴰ-intro λ y → map (F y) f ∘g π y
  map (⊕e Y F) f = ⊕ᴰ-elim λ y → σ y ∘g map (F y) f
  map (F ⊗e F') f = map F f ,⊗ map F' f
  map (∘e E F) f = E .F-hom (map F f)

  map-id : (F : Functor X) {A : X → Grammar}
         → map F (λ x → id {A x}) ≡ id
  map-id (k A) = refl
  map-id (Var x) = refl
  map-id (&e Y F) = &ᴰ≡ λ y →
    &ᴰ-β _ y
    ∙ cong (_∘g π y) (map-id (F y))
    ∙ ∘g-idL (π y)
    ∙ sym (∘g-idR (π y))
  map-id (⊕e Y F) = ⊕ᴰ≡ λ y →
    ⊕ᴰ-β _ y
    ∙ cong (σ y ∘g_) (map-id (F y))
    ∙ ∘g-idR (σ y)
    ∙ sym (∘g-idL (σ y))
  map-id (F ⊗e F') =
    cong₂ _,⊗_ (map-id F) (map-id F') ∙ ,⊗-id
  map-id (∘e E F) = cong (E .F-hom) (map-id F) ∙ E .F-id

  map-∘ : (F : Functor X) {A B C' : X → Grammar}
        → (f : ∀ x → B x ⊢ C' x) (f' : ∀ x → A x ⊢ B x)
        → map F (λ x → f x ∘g f' x) ≡ map F f ∘g map F f'
  map-∘ (k A) f f' = sym (∘g-idL id)
  map-∘ (Var x) f f' = refl
  map-∘ (&e Y F) f f' = &ᴰ≡ λ y →
    &ᴰ-β _ y
    ∙ cong (_∘g π y) (map-∘ (F y) f f')
    ∙ ∘g-assoc _ _ _
    ∙ cong (map (F y) f ∘g_) (sym (&ᴰ-β _ y))
    ∙ sym (∘g-assoc _ _ _)
    ∙ cong (_∘g map (&e Y F) f') (sym (&ᴰ-β _ y))
    ∙ ∘g-assoc _ _ _
  map-∘ (⊕e Y F) f f' = ⊕ᴰ≡ λ y →
    ⊕ᴰ-β _ y
    ∙ cong (σ y ∘g_) (map-∘ (F y) f f')
    ∙ sym (∘g-assoc _ _ _)
    ∙ cong (_∘g map (F y) f') (sym (⊕ᴰ-β _ y))
    ∙ ∘g-assoc _ _ _
    ∙ cong (map (⊕e Y F) f ∘g_) (sym (⊕ᴰ-β _ y))
    ∙ sym (∘g-assoc _ _ _)
  map-∘ (F ⊗e F') f f' =
    cong₂ _,⊗_ (map-∘ F f f') (map-∘ F' f f') ∙ ,⊗-seq _ _ _ _
  map-∘ (∘e E F) f f' =
    cong (E .F-hom) (map-∘ F f f') ∙ E .F-seq (map F f') (map F f)
