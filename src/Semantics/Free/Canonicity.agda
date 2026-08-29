{-# OPTIONS --lossy-unification #-}
{- Canonicity, as a displayed model over the syntax.

   The fibre over `A` is a predicate on the terms `Exp Γ A`, for
   every `Γ`, *closed under precomposition* — a sub-presheaf of
   `よ A`, not a predicate on closed terms. Two things force this:

     - ⊸: a global element of `B ⊸ D` is a morphism `B ⊢ D`, so
       knowing it is canonical means knowing what it does to
       canonical `B`s in arbitrary contexts;
     - the unitors: `η` moves a canonical term along a map between
       contexts, which needs the predicate to travel.

   Predicates are `hProp`-valued, so every displayed *law* is free
   (displayed homs are Π-types into props, hence props). Only the
   maps carry content.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Semantics.Free.Canonicity {ℓ} (Gen : hSet ℓ) where

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base

open import Semantics.Free.Syntax Gen
open import Semantics.Free.Model Gen

private
  ℓP : Level
  ℓP = ℓ-suc ℓ

-- | | A canonicity predicate: a sub-presheaf of `よ A`.
record Pred (A : Ty) : Type (ℓ-suc ℓP) where
  field
    ⟦_⟧P : (Γ : Ty) → Exp Γ A → hProp ℓP
    subst-closed : ∀ {Γ Δ} (m : Exp Δ Γ) (t : Exp Γ A)
                 → ⟨ ⟦ Γ ⟧P t ⟩ → ⟨ ⟦ Δ ⟧P (m ⋆E t) ⟩

open Pred public

module _ {A B : Ty} (P : Pred A) (Q : Pred B) where
  PredHom : Exp A B → Type ℓP
  PredHom f = ∀ Γ (t : Exp Γ A) → ⟨ P .⟦_⟧P Γ t ⟩ → ⟨ Q .⟦_⟧P Γ (t ⋆E f) ⟩

  isPropPredHom : ∀ f → isProp (PredHom f)
  isPropPredHom f =
    isPropΠ λ Γ → isPropΠ λ t → isPropΠ λ _ → Q .⟦_⟧P Γ _ .snd

open Categoryᴰ

CANON : Categoryᴰ FREE (ℓ-suc ℓP) ℓP
CANON .ob[_] = Pred
CANON .Hom[_][_,_] f P Q = PredHom P Q f
CANON .idᴰ {p = P} Γ t p = subst (λ z → ⟨ P .⟦_⟧P Γ z ⟩) (sym (⋆IdRE t)) p
CANON ._⋆ᴰ_ {f = f} {g = g} {zᴰ = R} fᴰ gᴰ Γ t p =
  subst (λ z → ⟨ R .⟦_⟧P Γ z ⟩) (⋆AssocE t f g) (gᴰ Γ (t ⋆E f) (fᴰ Γ t p))
CANON .⋆IdLᴰ {xᴰ = P} {yᴰ = Q} fᴰ =
  isProp→PathP (λ i → isPropPredHom P Q _) _ _
CANON .⋆IdRᴰ {xᴰ = P} {yᴰ = Q} fᴰ =
  isProp→PathP (λ i → isPropPredHom P Q _) _ _
CANON .⋆Assocᴰ {xᴰ = P} {wᴰ = S} fᴰ gᴰ hᴰ =
  isProp→PathP (λ i → isPropPredHom P S _) _ _
CANON .isSetHomᴰ {xᴰ = P} {yᴰ = Q} = isProp→isSet (isPropPredHom P Q _)

------------------------------------------------------------
-- The tensor: Day convolution
--
-- `t` is canonical when it factors through a tensor of contexts
-- as a tensor of canonical terms. This is the coend formula, and
-- it is what the *cartesian* gluing arguments get to replace by a
-- pointwise conjunction.
------------------------------------------------------------

module _ {A B : Ty} (P : Pred A) (Q : Pred B) where
  private
    Day : (Γ : Ty) → Exp Γ (A ⊗T B) → Type ℓP
    Day Γ t =
      ∥ Σ[ Γ₁ ∈ Ty ] Σ[ Γ₂ ∈ Ty ] Σ[ m ∈ Exp Γ (Γ₁ ⊗T Γ₂) ]
        Σ[ a ∈ Exp Γ₁ A ] Σ[ b ∈ Exp Γ₂ B ]
          (⟨ P .⟦_⟧P Γ₁ a ⟩ × ⟨ Q .⟦_⟧P Γ₂ b ⟩ × (t ≡ m ⋆E (a ⊗E b))) ∥₁

  _⊗P_ : Pred (A ⊗T B)
  _⊗P_ .⟦_⟧P Γ t = Day Γ t , squash₁
  _⊗P_ .subst-closed m t =
    PT.map λ (Γ₁ , Γ₂ , n , a , b , pa , pb , e) →
      Γ₁ , Γ₂ , m ⋆E n , a , b , pa , pb ,
      cong (m ⋆E_) e ∙ sym (⋆AssocE m n (a ⊗E b))

-- | The unit: every term of type ε is canonical.
εP : Pred εT
εP .⟦_⟧P Γ t = Unit* , isPropUnit*
εP .subst-closed m t p = tt*

-- | The tensor's action on morphisms: map the two factors.
module _ {A A' B B' : Ty} {P : Pred A} {P' : Pred A'}
  {Q : Pred B} {Q' : Pred B'} {f : Exp A A'} {g : Exp B B'}
  (fᴰ : PredHom P P' f) (gᴰ : PredHom Q Q' g)
  where
  ⊗Pmap : PredHom (P ⊗P Q) (P' ⊗P Q') (f ⊗E g)
  ⊗Pmap Γ t =
    PT.map λ (Γ₁ , Γ₂ , m , a , b , pa , pb , e) →
      Γ₁ , Γ₂ , m , a ⋆E f , b ⋆E g , fᴰ Γ₁ a pa , gᴰ Γ₂ b pb ,
      (cong (_⋆E (f ⊗E g)) e
       ∙ ⋆AssocE m (a ⊗E b) (f ⊗E g)
       ∙ cong (m ⋆E_) (sym (⊗E-seq a f b g)))
