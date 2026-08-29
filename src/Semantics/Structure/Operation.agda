{-# OPTIONS --lossy-unification #-}
{- A signature acting on a category.

   `Operations Sig C` interprets each operation `o` of the signature as
   a functor `C^(Arity o) → C`. Fixing all but the i-th argument gives
   an endofunctor `slot o i γ` of C; the operation is *closed in slot i*
   when that endofunctor has a right adjoint.

   For the theory of monoids the two slots of ⊗ give exactly ⊸ and ⟜
   (see `Semantics.Instances.MonoidSignature`), so this is the
   theory-generic form of "monoidal biclosed".

   No equations are imposed. Everything below — in particular the fact
   that every operation distributes over set-indexed sums in every
   slot — holds for the bare operations, before any theory's laws are
   considered.
-}
module Semantics.Structure.Operation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary.Base

open import Cubical.Categories.Category
open import Cubical.Categories.Functor using (Functor)
open import Cubical.Categories.Adjoint.UniversalElements

open import Semantics.Signature
open import Semantics.Structure.IndexedCoproduct
open import Semantics.Structure.Preservation

private
  variable
    ℓO ℓA ℓ ℓ' ℓX : Level

open Functor

module _ (Sig : Signature ℓO ℓA) (C : Category ℓ ℓ') where
  open Signature Sig
  private module C = Category C

  record Operations : Type (ℓ-max (ℓ-max ℓO ℓA) (ℓ-max ℓ ℓ')) where
    field
      ⟦_⟧₀ : (o : Op) → (Arity o → C.ob) → C.ob
      ⟦_⟧₁ : (o : Op) {γ δ : Arity o → C.ob}
           → (∀ i → C [ γ i , δ i ]) → C [ ⟦ o ⟧₀ γ , ⟦ o ⟧₀ δ ]
      ⟦⟧-id : (o : Op) {γ : Arity o → C.ob}
            → ⟦ o ⟧₁ (λ i → C.id {γ i}) ≡ C.id
      ⟦⟧-seq : (o : Op) {γ δ ε : Arity o → C.ob}
             → (f : ∀ i → C [ γ i , δ i ]) (g : ∀ i → C [ δ i , ε i ])
             → ⟦ o ⟧₁ (λ i → f i C.⋆ g i) ≡ ⟦ o ⟧₁ f C.⋆ ⟦ o ⟧₁ g

    ----------------------------------------------------------------
    -- Varying one argument
    ----------------------------------------------------------------
    module _ (o : Op) (i : Arity o) (γ : Arity o → C.ob) where
      private
        updHomD : {b b' : C.ob} (f : C [ b , b' ]) (j : Arity o)
                → (d : Dec (j ≡ i))
                → C [ caseDec d b (γ j) , caseDec d b' (γ j) ]
        updHomD f j (yes _) = f
        updHomD f j (no _) = C.id

      updHom : {b b' : C.ob} → C [ b , b' ]
             → (j : Arity o) → C [ upd γ i b j , upd γ i b' j ]
      updHom f j = updHomD f j (DiscreteArity o j i)

      private
        updHom-id : {b : C.ob} → updHom (C.id {b}) ≡ λ j → C.id
        updHom-id {b} = funExt λ j → lem j (DiscreteArity o j i)
          where
          lem : ∀ j d → updHomD (C.id {b}) j d ≡ C.id
          lem j (yes _) = refl
          lem j (no _) = refl

        updHom-seq : {b b' b'' : C.ob}
          (f : C [ b , b' ]) (g : C [ b' , b'' ])
          → updHom (f C.⋆ g) ≡ λ j → updHom f j C.⋆ updHom g j
        updHom-seq f g = funExt λ j → lem j (DiscreteArity o j i)
          where
          lem : ∀ j d → updHomD (f C.⋆ g) j d
                      ≡ updHomD f j d C.⋆ updHomD g j d
          lem j (yes _) = refl
          lem j (no _) = sym (C.⋆IdL C.id)

      -- The endofunctor "apply o, varying only the i-th argument".
      slot : Functor C C
      slot .F-ob b = ⟦ o ⟧₀ (upd γ i b)
      slot .F-hom f = ⟦ o ⟧₁ (updHom f)
      slot .F-id = cong ⟦ o ⟧₁ updHom-id ∙ ⟦⟧-id o
      slot .F-seq f g = cong ⟦ o ⟧₁ (updHom-seq f g) ∙ ⟦⟧-seq o _ _

  ------------------------------------------------------------------
  -- Closure in every slot: the theory-generic biclosure.
  ------------------------------------------------------------------
  record ClosedOps (Ops : Operations) : Type (ℓ-max (ℓ-max ℓO ℓA) (ℓ-max ℓ ℓ')) where
    open Operations Ops
    field
      closed : (o : Op) (i : Arity o) (γ : Arity o → C.ob) (d : C.ob)
             → RightAdjointAt (slot o i γ) d

    ----------------------------------------------------------------
    -- Consequently every operation distributes over set-indexed sums
    -- in every one of its arguments.
    ----------------------------------------------------------------
    module _ (o : Op) (i : Arity o) (γ : Arity o → C.ob)
      {X : hSet ℓX} {A : ⟨ X ⟩ → C.ob}
      (ΣA : ΣTy C A)
      (ΣopA : ΣTy C (λ x → ⟦ o ⟧₀ (upd γ i (A x)))) where

      open PreserveΣ (slot o i γ) (closed o i γ) ΣA ΣopA public
        renaming ( preserve to op-dist
                 ; preserve⁻ to op-dist⁻
                 ; preserve-β to op-dist-β
                 ; preserve-sec to op-dist-sec
                 ; preserve-ret to op-dist-ret )
