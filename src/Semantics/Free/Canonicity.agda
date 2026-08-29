{-# OPTIONS --lossy-unification #-}
{- Canonicity, as a displayed model over the syntax.

   The fibre over a type `A` is a predicate on the terms `Exp Γ A`,
   for every `Γ` — a *sub-presheaf* of `よ A`, not a predicate on
   closed terms only. That is forced by ⊸: a global element of
   `B ⊸ D` is a morphism `B ⊢ D`, so knowing it is canonical means
   knowing what it does to canonical `B`s in arbitrary contexts.

   Predicates are `hProp`-valued. That makes every displayed law
   free — the displayed hom types are Π-types into props, hence
   props — so the only content per connective is the introduction
   direction. (Same trick that made `Instances.Languages` cheap.)
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Semantics.Free.Canonicity {ℓ} (Gen : hSet ℓ) where

open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base

open import Semantics.Free.Syntax Gen
open import Semantics.Free.Model Gen

private
  ℓP : Level
  ℓP = ℓ-suc ℓ

-- | A canonicity predicate on the terms of type `A`.
Pred : Ty → Type (ℓ-suc ℓP)
Pred A = (Γ : Ty) → Exp Γ A → hProp ℓP

module _ {A B : Ty} (P : Pred A) (Q : Pred B) where
  PredHom : Exp A B → Type ℓP
  PredHom f = ∀ Γ (t : Exp Γ A) → ⟨ P Γ t ⟩ → ⟨ Q Γ (t ⋆E f) ⟩

  isPropPredHom : ∀ f → isProp (PredHom f)
  isPropPredHom f =
    isPropΠ λ Γ → isPropΠ λ t → isPropΠ λ _ → Q Γ _ .snd

open Categoryᴰ

-- | Terms of the syntax, displayed over a canonicity predicate.
CANON : Categoryᴰ FREE (ℓ-suc ℓP) ℓP
CANON .ob[_] = Pred
CANON .Hom[_][_,_] f P Q = PredHom P Q f
CANON .idᴰ {p = P} Γ t p = subst (λ z → ⟨ P Γ z ⟩) (sym (⋆IdRE t)) p
CANON ._⋆ᴰ_ {f = f} {g = g} {yᴰ = Q} {zᴰ = R} fᴰ gᴰ Γ t p =
  subst (λ z → ⟨ R Γ z ⟩) (⋆AssocE t f g) (gᴰ Γ (t ⋆E f) (fᴰ Γ t p))
CANON .⋆IdLᴰ {yᴰ = Q} fᴰ =
  isProp→PathP (λ i → isPropPredHom _ Q _) _ _
CANON .⋆IdRᴰ {yᴰ = Q} fᴰ =
  isProp→PathP (λ i → isPropPredHom _ Q _) _ _
CANON .⋆Assocᴰ {wᴰ = S} fᴰ gᴰ hᴰ =
  isProp→PathP (λ i → isPropPredHom _ S _) _ _
CANON .isSetHomᴰ {yᴰ = Q} =
  isProp→isSet (isPropPredHom _ Q _)

------------------------------------------------------------------
-- The tensor: Day convolution
--
-- `t : Exp Γ (A ⊗T B)` is canonical when it factors through a
-- tensor of contexts as a tensor of canonical terms. This is the
-- coend formula for Day convolution of presheaves, and it is what
-- the *cartesian* gluing arguments get to replace by a pointwise
-- conjunction.
------------------------------------------------------------------

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation as PT

module _ {A B : Ty} (P : Pred A) (Q : Pred B) where
  _⊗P_ : Pred (A ⊗T B)
  _⊗P_ Γ t =
    ∥ Σ[ Γ₁ ∈ Ty ] Σ[ Γ₂ ∈ Ty ] Σ[ m ∈ Exp Γ (Γ₁ ⊗T Γ₂) ]
      Σ[ a ∈ Exp Γ₁ A ] Σ[ b ∈ Exp Γ₂ B ]
        (⟨ P Γ₁ a ⟩ × ⟨ Q Γ₂ b ⟩ × (t ≡ m ⋆E (a ⊗E b))) ∥₁
    , squash₁

-- | The unit: every term of type ε is canonical.
εP : Pred εT
εP Γ t = Unit* , isPropUnit*
