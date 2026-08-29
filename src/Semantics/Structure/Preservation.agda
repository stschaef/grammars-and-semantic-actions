{-# OPTIONS --lossy-unification #-}
{- Left adjoints preserve set-indexed coproducts.

   Stated once, for an arbitrary endofunctor with a right adjoint. Every
   distributivity law in the DSL is an instance:

     - ⊗ over ⊕ᴰ on the left  : E = (- ⊗ B), right adjoint B ⊸ -
     - ⊗ over ⊕ᴰ on the right : E = (A ⊗ -), right adjoint - ⟜ A
     - any operation of any algebraic theory, in any of its argument
       slots (see `Semantics.Structure.Operation`).
-}
module Semantics.Structure.Preservation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Functor using (Functor)
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Limits.IndexedProduct.Base

open import Semantics.Structure.IndexedCoproduct

private
  variable
    ℓ ℓ' ℓX : Level

open Functor

module PreserveΣ {C : Category ℓ ℓ'} (E : Functor C C)
  (radj : ∀ d → RightAdjointAt E d)
  {X : hSet ℓX} {A : ⟨ X ⟩ → Category.ob C}
  (ΣA : ΣTy C A) (ΣEA : ΣTy C (λ x → E .F-ob (A x))) where

  private
    module C = Category C
    module R (d : C.ob) = UniversalElementNotation (radj d)
    module a = ΣTyNotation A ΣA
    module ea = ΣTyNotation (λ x → E .F-ob (A x)) ΣEA

    Rβ : ∀ {b d} {p : C [ E .F-ob b , d ]}
       → E .F-hom (R.intro d p) C.⋆ R.element d ≡ p
    Rβ {d = d} = R.β d

    Rnat : ∀ {b b' d} {f : C [ b' , b ]} {p : C [ E .F-ob b , d ]}
         → f C.⋆ R.intro d p ≡ R.intro d (E .F-hom f C.⋆ p)
    Rnat {d = d} = R.intro-natural d

  -- Maps out of E applied to a coproduct are determined componentwise.
  E⊕ext : {D : C.ob} {f f' : C [ E .F-ob a.vertex , D ]}
        → (∀ x → E .F-hom (a.σ x) C.⋆ f ≡ E .F-hom (a.σ x) C.⋆ f')
        → f ≡ f'
  E⊕ext {D = D} {f = f} {f' = f'} p =
    sym Rβ ∙ cong (λ z → E .F-hom z C.⋆ R.element D) q ∙ Rβ
    where
    q : R.intro D f ≡ R.intro D f'
    q = a.⊕ext λ x → Rnat ∙ cong (R.intro D) (p x) ∙ sym Rnat

  preserve⁻ : C [ ea.vertex , E .F-ob a.vertex ]
  preserve⁻ = ea.elim λ x → E .F-hom (a.σ x)

  preserve : C [ E .F-ob a.vertex , ea.vertex ]
  preserve =
    E .F-hom (a.elim λ x → R.intro ea.vertex (ea.σ x))
      C.⋆ R.element ea.vertex

  preserve-β : ∀ x → E .F-hom (a.σ x) C.⋆ preserve ≡ ea.σ x
  preserve-β x =
    sym (C.⋆Assoc _ _ _)
    ∙ cong (C._⋆ R.element ea.vertex)
           (sym (E .F-seq _ _) ∙ cong (E .F-hom) (a.⊕β _ x))
    ∙ Rβ

  preserve-sec : preserve⁻ C.⋆ preserve ≡ C.id
  preserve-sec = ea.⊕ext λ x →
    sym (C.⋆Assoc _ _ _)
    ∙ cong (C._⋆ preserve) (ea.⊕β _ x)
    ∙ preserve-β x
    ∙ sym (C.⋆IdR _)

  preserve-ret : preserve C.⋆ preserve⁻ ≡ C.id
  preserve-ret = E⊕ext λ x →
    sym (C.⋆Assoc _ _ _)
    ∙ cong (C._⋆ preserve⁻) (preserve-β x)
    ∙ ea.⊕β _ x
    ∙ sym (C.⋆IdR _)
