{-# OPTIONS --lossy-unification #-}
{- The associator, the pentagon, and the assembled displayed monoidal
   structure. See `Semantics.Displayed.ReindexMonoidal.Base` for the
   tensor, the structure maps, and the unitor coherences.
-}
module Semantics.Displayed.ReindexMonoidal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Monoidal.Functor
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.TotalCategory using (∫C)

open import Cubical.Categories.Displayed.Base
import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.Monoidal.Base
open import Cubical.Categories.Displayed.Instances.Reindex.Base using (reindex)
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration using (isFibration)

open import Semantics.Displayed.IsoLift
open import Semantics.Displayed.ReindexMonoidal.Base

private
  variable
    ℓM ℓM' ℓN ℓN' ℓCᴰ ℓCᴰ' : Level

open Functor
open Functorᴰ
open NatTrans
open NatIso
open NatIsoᴰ
open NatTransᴰ
open isIso
open isIsoᴰ

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
    Rᴰ : Categoryᴰ M.C ℓCᴰ ℓCᴰ'
    Rᴰ = reindex Cᴰ G.F

    module Rᴰ = Fibers Rᴰ

  open Reindex P G cartLifts public
  open IsoLifts Cᴰ cartLifts

  private
    ε≅ : CatIso N.C (G.F ⟅ M.unit ⟆) N.unit
    ε≅ = invIso G.ε-Iso

    μ≅ : ∀ x y → CatIso N.C (G.F ⟅ x M.⊗ y ⟆) ((G.F ⟅ x ⟆) N.⊗ (G.F ⟅ y ⟆))
    μ≅ x y = invIso (NatIsoAt G.μ-Iso (x , y))

  private
    -- Naturality of the reindexed associator. Both sides reduce to the
    -- same normal form: the μ-lifts cancel in pairs and what is left is
    -- naturality of `P.αᴰ`.
    α'-nat : ∀ {x₁ y₁ x₂ y₂ x₃ y₃}
      {f : M.C [ x₁ , y₁ ]}{g : M.C [ x₂ , y₂ ]}{h : M.C [ x₃ , y₃ ]}
      {x₁ᴰ : Rᴰ.ob[ x₁ ]}{y₁ᴰ : Rᴰ.ob[ y₁ ]}
      {x₂ᴰ : Rᴰ.ob[ x₂ ]}{y₂ᴰ : Rᴰ.ob[ y₂ ]}
      {x₃ᴰ : Rᴰ.ob[ x₃ ]}{y₃ᴰ : Rᴰ.ob[ y₃ ]}
      (fᴰ : Rᴰ.Hom[ f ][ x₁ᴰ , y₁ᴰ ])
      (gᴰ : Rᴰ.Hom[ g ][ x₂ᴰ , y₂ᴰ ])
      (hᴰ : Rᴰ.Hom[ h ][ x₃ᴰ , y₃ᴰ ])
      → ((─⊗ᴰ'─ .F-homᴰ (fᴰ , ─⊗ᴰ'─ .F-homᴰ (gᴰ , hᴰ)))
          Rᴰ.⋆ᴰ αᴰ'⟨ y₁ᴰ , y₂ᴰ , y₃ᴰ ⟩)
          Rᴰ.≡[ M.α .trans .N-hom (f , (g , h)) ]
        (αᴰ'⟨ x₁ᴰ , x₂ᴰ , x₃ᴰ ⟩
          Rᴰ.⋆ᴰ (─⊗ᴰ'─ .F-homᴰ (─⊗ᴰ'─ .F-homᴰ (fᴰ , gᴰ) , hᴰ)))
    α'-nat fᴰ gᴰ hᴰ = Cᴰ.rectify $ Cᴰ.≡out $
      -- left-hand side down to the normal form
        sym (R.reind-filler _ _)
      ∙ Cᴰ.⟨ sym (R.reind-filler _ _) ⟩⋆⟨ sym (R.reind-filler _ _) ⟩
      ∙ Cᴰ.⋆Assoc _ _ _
      ∙ Cᴰ.⟨ refl ⟩⋆⟨
            Cᴰ.⋆Assoc _ _ _
          ∙ Cᴰ.⟨ refl ⟩⋆⟨ sym (Cᴰ.⋆Assoc _ _ _)
                        ∙ Cᴰ.⟨ Cᴰ.≡in (liftIn⋆Out (μ≅ _ _) _) ⟩⋆⟨ refl ⟩
                        ∙ Cᴰ.⋆IdL _ ⟩
          ∙ sym (Cᴰ.⋆Assoc _ _ _)
          ∙ Cᴰ.⟨ sym (Cᴰ.≡in (P.─⊗ᴰ─ .F-seqᴰ _ _))
               ∙ ⟨ Cᴰ.⋆IdR _ ∙ sym (Cᴰ.⋆IdL _) ⟩⊗ₕᴰ⟨
                   Cᴰ.⟨ sym (R.reind-filler _ _) ⟩⋆⟨ refl ⟩
                 ∙ Cᴰ.⋆Assoc _ _ _
                 ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⋆Assoc _ _ _
                               ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.≡in (liftIn⋆Out (μ≅ _ _) _) ⟩
                               ∙ Cᴰ.⋆IdR _ ⟩ ⟩
               ∙ Cᴰ.≡in (P.─⊗ᴰ─ .F-seqᴰ _ _) ⟩⋆⟨ refl ⟩
          ∙ Cᴰ.⋆Assoc _ _ _
          ∙ Cᴰ.⟨ refl ⟩⋆⟨ sym (Cᴰ.⋆Assoc _ _ _)
                        ∙ Cᴰ.⟨ Cᴰ.≡in (P.αᴰ .transᴰ .N-homᴰ (fᴰ , (gᴰ , hᴰ))) ⟩⋆⟨ refl ⟩
                        ∙ Cᴰ.⋆Assoc _ _ _
                        ∙ Cᴰ.⟨ refl ⟩⋆⟨
                              sym (Cᴰ.⋆Assoc _ _ _)
                            ∙ Cᴰ.⟨ sym (Cᴰ.≡in (P.─⊗ᴰ─ .F-seqᴰ _ _))
                                 ∙ ⟨ refl ⟩⊗ₕᴰ⟨ Cᴰ.⋆IdR _ ⟩ ⟩⋆⟨ refl ⟩ ⟩ ⟩ ⟩
      -- right-hand side down to the same normal form, reversed
      ∙ sym (
          sym (R.reind-filler _ _)
        ∙ Cᴰ.⟨ sym (R.reind-filler _ _) ⟩⋆⟨ sym (R.reind-filler _ _) ⟩
        ∙ Cᴰ.⋆Assoc _ _ _
        ∙ Cᴰ.⟨ refl ⟩⋆⟨
              Cᴰ.⋆Assoc _ _ _
            ∙ Cᴰ.⟨ refl ⟩⋆⟨
                  Cᴰ.⋆Assoc _ _ _
                ∙ Cᴰ.⟨ refl ⟩⋆⟨
                      Cᴰ.⋆Assoc _ _ _
                    ∙ Cᴰ.⟨ refl ⟩⋆⟨ sym (Cᴰ.⋆Assoc _ _ _)
                                  ∙ Cᴰ.⟨ Cᴰ.≡in (liftIn⋆Out (μ≅ _ _) _) ⟩⋆⟨ refl ⟩
                                  ∙ Cᴰ.⋆IdL _ ⟩
                    ∙ sym (Cᴰ.⋆Assoc _ _ _)
                    ∙ Cᴰ.⟨ sym (Cᴰ.≡in (P.─⊗ᴰ─ .F-seqᴰ _ _))
                         ∙ ⟨ Cᴰ.⟨ refl ⟩⋆⟨ sym (R.reind-filler _ _) ⟩
                           ∙ sym (Cᴰ.⋆Assoc _ _ _)
                           ∙ Cᴰ.⟨ Cᴰ.≡in (liftIn⋆Out (μ≅ _ _) _) ⟩⋆⟨ refl ⟩
                           ∙ Cᴰ.⋆IdL _ ⟩⊗ₕᴰ⟨ Cᴰ.⋆IdL _ ⟩ ⟩⋆⟨ refl ⟩ ⟩ ⟩ ⟩)
