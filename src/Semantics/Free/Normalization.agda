{-# OPTIONS --lossy-unification #-}
{- Proof-relevant gluing over the syntax: Artin gluing.

   The prop-valued version (`Semantics.Free.Canonicity`) proves
   canonicity — *that* a canonical form exists. For normalisation
   we need *which*, so the fibres must be sets, and then no
   displayed law is free any more.

   The formulation that keeps that affordable is Artin gluing
   rather than raw families over terms: the fibre over `A` is a
   presheaf on the syntax together with a map to `よ A`, and a
   displayed morphism is a presheaf map commuting with those. The
   category laws then come from the presheaf category, and the
   commuting conditions are equations between `PshHom`s — which
   live in a *set*, so they are props and `Σ≡Prop` discharges
   them.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Semantics.Free.Normalization {ℓ} (Gen : hSet ℓ) where

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets using (_[-,_])
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Displayed.Base

open import Semantics.Free.Syntax Gen
open import Semantics.Free.Model Gen

private
  ℓP : Level
  ℓP = ℓ-suc ℓ

-- | A glued object over `A`: a presheaf on the syntax with a map
--   to the representable. Proof-relevant, unlike a sub-presheaf.
Glued : Ty → Type (ℓ-suc ℓP)
Glued A = Σ[ P ∈ Presheaf FREE ℓP ] PshHom P (FREE [-, A ])

open PshHom

-- | The representable's action: postcomposition.
よ⟪_⟫ : {A B : Ty} → Exp A B → PshHom (FREE [-, A ]) (FREE [-, B ])
よ⟪ f ⟫ .N-ob Γ t = t ⋆E f
よ⟪ f ⟫ .N-hom Γ Δ m t = ⋆AssocE m t f

module _ {A B : Ty} ((P , p) : Glued A) ((Q , q) : Glued B) where
  GluedHom : Exp A B → Type ℓP
  GluedHom f =
    Σ[ α ∈ PshHom P Q ] (α ⋆PshHom q ≡ p ⋆PshHom よ⟪ f ⟫)
