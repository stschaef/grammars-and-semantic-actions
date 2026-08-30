{-# OPTIONS --lossy-unification --allow-unsolved-metas #-}
{- Reindexing a displayed biclosed structure along a strong monoidal
   functor that preserves ⊸ and ⟜.

   ccl's `reindex-reflects-UMPᴰ` does the work: it reflects a displayed
   universal element along a functor preserving the base one. All that
   is left is to identify the displayed presheaf it produces with the
   one `RightAdjointAtᴰ` asks for, which differs by the μ-lift — the
   same conjugation as in `Semantics.Displayed.ReindexMonoidal`.

   As in ccl's `reflectsBPᴰ`, the hypothesis is stated at the
   *transported* universal element rather than at `N`'s own ⊸, which is
   what `reindex-reflects-UMPᴰ` consumes.
-}
module Semantics.Displayed.ReindexBiclosed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.TotalCategory using (∫C)
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Monoidal.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Representable

open import Cubical.Categories.Displayed.Base
import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Monoidal.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration using (isFibration)
open import Cubical.Categories.Displayed.Instances.Reindex.Base using (reindex; π)
open import Cubical.Categories.Displayed.Instances.Reindex.UniversalProperties
  using (reindex-reflects-UMPᴰ)

open import Semantics.Displayed.CatLemmas
open import Semantics.Displayed.IsoLift
open import Semantics.Displayed.Model
import Semantics.Displayed.ReindexMonoidal as RM
open import Semantics.Displayed.ReindexMonoidal.Pentagon
open import Semantics.Displayed.RightAdjoint
open import Semantics.Structure.Biclosed
open import Semantics.Structure.BiclosedFunctor

private
  variable
    ℓM ℓM' ℓN ℓN' ℓCᴰ ℓCᴰ' : Level

open Functor
open Functorᴰ
open NatTrans
open PshHom
open PshIso
open UniversalElement

module _ {M : MonoidalCategory ℓM ℓM'} {N : MonoidalCategory ℓN ℓN'}
  {Cᴰ : Categoryᴰ (MonoidalCategory.C N) ℓCᴰ ℓCᴰ'}
  (P : MonoidalStrᴰ N Cᴰ)
  (G : StrongMonoidalFunctor M N)
  (cartLifts : isFibration Cᴰ)
  where
  private
    module M = MonoidalCategory M
    module N = MonoidalCategory N
    module Cᴰ = Fibers Cᴰ
    module R = HomᴰReasoning Cᴰ
    module P = MonoidalStrᴰ P
    module G = StrongMonoidalFunctor G

  open Pentagon P G cartLifts public
  open IsoLifts Cᴰ cartLifts

  -- | The comparison between the displayed presheaf that
  --   `reindex-reflects-UMPᴰ` produces and the one `⊸Atᴰ` wants: they
  --   differ by the μ-lift on the source.
  ⊸Comparison : ∀ {B D} (Bᴰ : Cᴰ.ob[ G.F ⟅ B ⟆ ]) (Dᴰ : Cᴰ.ob[ G.F ⟅ D ⟆ ])
    → PshIsoⱽ
        (reindPsh (π Cᴰ G.F /Fᴰ ⊸Het G B D)
          (RightAdjointProfᴰ (tensorRᴰ N P Bᴰ) Dᴰ))
        (RightAdjointProfᴰ (tensorRᴰ M (RM.reindexMonoidalStrᴰ P G cartLifts) Bᴰ) Dᴰ)
  ⊸Comparison {B} {D} Bᴰ Dᴰ = Isos→PshIso
    (λ { (Γ , Γᴰ , f) → iso
      (λ h → R.reind (base⊸ f) (liftOut (μ≅ Γ B) _ Cᴰ.⋆ᴰ h))
      (λ k → liftIn (μ≅ Γ B) _ Cᴰ.⋆ᴰ k)
      (λ k → Cᴰ.rectify $ Cᴰ.≡out $
          sym (R.reind-filler _ _)
        ∙ sym (Cᴰ.⋆Assoc _ _ _)
        ∙ Cᴰ.⟨ Cᴰ.≡in (liftOut⋆In (μ≅ Γ B) _) ⟩⋆⟨ refl ⟩
        ∙ Cᴰ.⋆IdL _)
      (λ h → Cᴰ.rectify $ Cᴰ.≡out $
          Cᴰ.⟨ refl ⟩⋆⟨ sym (R.reind-filler _ _) ⟩
        ∙ sym (Cᴰ.⋆Assoc _ _ _)
        ∙ Cᴰ.⟨ Cᴰ.≡in (liftIn⋆Out (μ≅ Γ B) _) ⟩⋆⟨ refl ⟩
        ∙ Cᴰ.⋆IdL _) })
    -- Outstanding. Both sides are the same composite of liftOut,
    -- (γᴰ ⊗ₕᴰ idᴰ) and h, with the middle liftIn ⋆ liftOut cancelling
    -- (`⋆cancelL`); the right-hand side additionally carries the ⊗ᴰ and
    -- Rᴰ.⋆ᴰ reinds. `sym (R.reind-filler _ _)` handles the left-hand
    -- outer reind (checked), but the right-hand outer one comes from
    -- the presheaf's contravariant action and so lives in a different
    -- reasoning family; that is the only thing missing.
    {!!}
    where
    base⊸ : ∀ {Γ} (f : M.C [ Γ M.⊗ B , D ])
      → ((μ≅ Γ B) .fst N.⋆ (G.μ⟨ Γ , B ⟩ N.⋆ (G.F ⟪ f ⟫))) ≡ (G.F ⟪ f ⟫)
    base⊸ f = sym (N.⋆Assoc _ _ _)
            ∙ cong (N._⋆ (G.F ⟪ f ⟫)) (G.μ-isIso _ .isIso.sec)
            ∙ N.⋆IdL _
