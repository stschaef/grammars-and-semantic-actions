{-# OPTIONS --lossy-unification #-}
{- When a strong monoidal functor preserves the biclosed structure.

   `Semantics.Displayed.ReindexMonoidal` transports a displayed
   monoidal structure along a strong monoidal `G`. To transport a
   displayed *biclosed* structure as well, `G` has to preserve ⊸ and ⟜.

   ⊸ and ⟜ are `RightAdjointAt`s, i.e. universal elements, so "preserves"
   is ccl's `preservesUniversalElement` applied to the canonical
   comparison `PshHet`, which sends `f : Γ ⊗ B → D` to `μ⟨Γ,B⟩ ⋆ G f`.
   That comparison is forced, so only the two universality conditions
   are fields.

   The functor out of the free model satisfies this on the nose: its
   `μ` is the identity and it sends `B ⊸ D` to `⟦B⟧ ⊸ ⟦D⟧`.
-}
module Semantics.Structure.BiclosedFunctor where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Representable

open import Semantics.Structure.Biclosed

private
  variable
    ℓM ℓM' ℓN ℓN' : Level

open Functor
open NatTrans
open PshHom

module _ {M : MonoidalCategory ℓM ℓM'} {N : MonoidalCategory ℓN ℓN'}
  (G : StrongMonoidalFunctor M N)
  where
  private
    module M = MonoidalCategory M
    module N = MonoidalCategory N
    module G = StrongMonoidalFunctor G

  -- | `f : Γ ⊗ B → D`  ↦  `μ⟨Γ,B⟩ ⋆ G f : G Γ ⊗ G B → G D`.
  ⊸Het : ∀ B D
    → PshHet G.F (RightAdjointProf (tensorR M B) ⟅ D ⟆)
                 (RightAdjointProf (tensorR N (G.F ⟅ B ⟆)) ⟅ G.F ⟅ D ⟆ ⟆)
  ⊸Het B D .N-ob Γ f = G.μ⟨ Γ , B ⟩ N.⋆ (G.F ⟪ f ⟫)
  ⊸Het B D .N-hom Δ Γ g f =
      cong (G.μ⟨ Δ , B ⟩ N.⋆_) (G.F .F-seq _ _)
    ∙ sym (N.⋆Assoc _ _ _)
    ∙ cong (N._⋆ (G.F ⟪ f ⟫)) (sym (G.μ .N-hom (g , M.id)))
    ∙ cong (N._⋆ (G.F ⟪ f ⟫))
        (cong (λ h → ((G.F ⟪ g ⟫) N.⊗ₕ h) N.⋆ G.μ⟨ Γ , B ⟩) (G.F .F-id))
    ∙ N.⋆Assoc _ _ _

  -- | The mirror image: `f : A ⊗ Γ → D`  ↦  `μ⟨A,Γ⟩ ⋆ G f`.
  ⟜Het : ∀ A D
    → PshHet G.F (RightAdjointProf (tensorL M A) ⟅ D ⟆)
                 (RightAdjointProf (tensorL N (G.F ⟅ A ⟆)) ⟅ G.F ⟅ D ⟆ ⟆)
  ⟜Het A D .N-ob Γ f = G.μ⟨ A , Γ ⟩ N.⋆ (G.F ⟪ f ⟫)
  ⟜Het A D .N-hom Δ Γ g f =
      cong (G.μ⟨ A , Δ ⟩ N.⋆_) (G.F .F-seq _ _)
    ∙ sym (N.⋆Assoc _ _ _)
    ∙ cong (N._⋆ (G.F ⟪ f ⟫)) (sym (G.μ .N-hom (M.id , g)))
    ∙ cong (N._⋆ (G.F ⟪ f ⟫))
        (cong (λ h → (h N.⊗ₕ (G.F ⟪ g ⟫)) N.⋆ G.μ⟨ A , Γ ⟩) (G.F .F-id))
    ∙ N.⋆Assoc _ _ _

  -- | `G` preserves the biclosed structure: the comparison maps carry
  --   `M`'s ⊸/⟜ universal elements to `N`'s.
  record PreservesBiclosed (bcM : Biclosed M) : Type (ℓ-max (ℓ-max ℓM ℓM') (ℓ-max ℓN ℓN')) where
    private module bcM = Biclosed bcM
    field
      ⊸pres : ∀ B D → preservesUniversalElement (⊸Het B D) (bcM.⊸ues B D)
      ⟜pres : ∀ A D → preservesUniversalElement (⟜Het A D) (bcM.⟜ues A D)
