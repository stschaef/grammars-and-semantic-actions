{-# OPTIONS --lossy-unification #-}
{- The monoidal case of the theory-generic structure.

   A monoidal category with a biclosure is exactly a model of the
   signature of monoids whose operations are closed in every slot:

     - the nullary operation ε is interpreted by the monoidal unit
       (and has no slots to be closed in);
     - the binary operation ⊗ is interpreted by the tensor, and its two
       slot-closures are ⊸ (vary the left argument) and ⟜ (vary the
       right argument).

   Both closures are accepted here *definitionally*: `slot `⊗ true γ`
   computes to `- ⊗ γ false` and `slot `⊗ false γ` to `γ true ⊗ -`, so
   the universal elements from `Semantics.Structure.Biclosed` are
   literally the ones the signature layer asks for.
-}
module Semantics.Instances.MonoidSignature where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Bool using (Bool; true; false)
import Cubical.Data.Empty as Empty

open import Cubical.Categories.Category
open import Cubical.Categories.Functor using (Functor)
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Presheaf.Representable using (UniversalElement)

open import Semantics.Signature
open import Semantics.Structure.Biclosed
open import Semantics.Structure.Operation

private
  variable
    ℓ ℓ' : Level

open Functor
open Signature MonoidSig

module _ (M : MonoidalCategory ℓ ℓ') (bc : Biclosed M) where
  open MonoidalCategory M
  open Biclosed bc

  MonOps : Operations MonoidSig C
  MonOps = record
    { ⟦_⟧₀ = λ where
        `ε _ → unit
        `⊗ γ → γ true ⊗ γ false
    ; ⟦_⟧₁ = λ where
        `ε _ → id
        `⊗ f → f true ⊗ₕ f false
    ; ⟦⟧-id = λ where
        `ε → refl
        `⊗ → ─⊗─ .F-id
    ; ⟦⟧-seq = λ where
        `ε f g → sym (⋆IdL id)
        `⊗ f g → ─⊗─ .F-seq (f true , f false) (g true , g false)
    }

  open Operations MonOps
  MonClosed : ClosedOps MonoidSig C MonOps
  MonClosed = record { closed = cl }
    where
    open UniversalElement
    -- The slot functors compute to the two partial applications of the
    -- tensor, so the universal elements transfer field by field.
    cl : (o : Op) (i : Arity o) (γ : Arity o → ob) (d : ob)
       → RightAdjointAt (slot o i γ) d
    cl `ε () γ d
    -- varying the left factor: right adjoint is ⊸
    cl `⊗ true γ d .vertex = ⊸ues (γ false) d .vertex
    cl `⊗ true γ d .element = ⊸ues (γ false) d .element
    cl `⊗ true γ d .universal = ⊸ues (γ false) d .universal
    -- varying the right factor: right adjoint is ⟜
    cl `⊗ false γ d .vertex = ⟜ues (γ true) d .vertex
    cl `⊗ false γ d .element = ⟜ues (γ true) d .element
    cl `⊗ false γ d .universal = ⟜ues (γ true) d .universal
