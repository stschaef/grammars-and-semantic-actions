{-# OPTIONS --lossy-unification #-}
{- Naturality and invertibility of the reindexed associator.
   Split out from the assembly because these elaborate to very large
   terms.
-}
module Semantics.Displayed.ReindexMonoidal.Assoc where

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
open import Semantics.Displayed.CatLemmas
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

module Assoc {M : MonoidalCategory ℓM ℓM'} {N : MonoidalCategory ℓN ℓN'}
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

  -- Associator coherences.
  ε≅ : CatIso N.C (G.F ⟅ M.unit ⟆) N.unit
  ε≅ = invIso G.ε-Iso

  μ≅ : ∀ x y → CatIso N.C (G.F ⟅ x M.⊗ y ⟆) ((G.F ⟅ x ⟆) N.⊗ (G.F ⟅ y ⟆))
  μ≅ x y = invIso (NatIsoAt G.μ-Iso (x , y))

  -- Associator coherences.
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

  -- | `(k ⊗ id) ⋆ (k⁻ ⊗ id)` is the identity when `k ⋆ k⁻` is.
  ⊗L-inv : ∀ {a b c}{f : N.C [ a , b ]}{g : N.C [ b , a ]}
    {aᴰ : Cᴰ.ob[ a ]}{bᴰ : Cᴰ.ob[ b ]}{cᴰ : Cᴰ.ob[ c ]}
    {k : Cᴰ.Hom[ f ][ aᴰ , bᴰ ]}{k⁻ : Cᴰ.Hom[ g ][ bᴰ , aᴰ ]}
    → Path Cᴰ.Hom[ (a , aᴰ) , (a , aᴰ) ] (_ , k Cᴰ.⋆ᴰ k⁻) (N.id , Cᴰ.idᴰ)
    → Path Cᴰ.Hom[ (a N.⊗ c , aᴰ P.⊗ᴰ cᴰ) , (a N.⊗ c , aᴰ P.⊗ᴰ cᴰ) ]
        (_ , (k P.⊗ₕᴰ Cᴰ.idᴰ) Cᴰ.⋆ᴰ (k⁻ P.⊗ₕᴰ Cᴰ.idᴰ)) (N.id , Cᴰ.idᴰ)
  ⊗L-inv p = sym (Cᴰ.≡in (P.─⊗ᴰ─ .F-seqᴰ _ _))
           ∙ ⟨ p ⟩⊗ₕᴰ⟨ Cᴰ.⋆IdL _ ⟩
           ∙ Cᴰ.≡in (P.─⊗ᴰ─ .F-idᴰ)

  -- | The mirror image.
  ⊗R-inv : ∀ {a b c}{f : N.C [ a , b ]}{g : N.C [ b , a ]}
    {aᴰ : Cᴰ.ob[ a ]}{bᴰ : Cᴰ.ob[ b ]}{cᴰ : Cᴰ.ob[ c ]}
    {k : Cᴰ.Hom[ f ][ aᴰ , bᴰ ]}{k⁻ : Cᴰ.Hom[ g ][ bᴰ , aᴰ ]}
    → Path Cᴰ.Hom[ (a , aᴰ) , (a , aᴰ) ] (_ , k Cᴰ.⋆ᴰ k⁻) (N.id , Cᴰ.idᴰ)
    → Path Cᴰ.Hom[ (c N.⊗ a , cᴰ P.⊗ᴰ aᴰ) , (c N.⊗ a , cᴰ P.⊗ᴰ aᴰ) ]
        (_ , (Cᴰ.idᴰ P.⊗ₕᴰ k) Cᴰ.⋆ᴰ (Cᴰ.idᴰ P.⊗ₕᴰ k⁻)) (N.id , Cᴰ.idᴰ)
  ⊗R-inv p = sym (Cᴰ.≡in (P.─⊗ᴰ─ .F-seqᴰ _ _))
           ∙ ⟨ Cᴰ.⋆IdL _ ⟩⊗ₕᴰ⟨ p ⟩
           ∙ Cᴰ.≡in (P.─⊗ᴰ─ .F-idᴰ)

  -- | Regroup `k ⋆ (x ⋆ (y ⋆ m))` as `k ⋆ ((x ⋆ y) ⋆ m)`: the shape
  --   `conjSeq` expects.
  regroup : ∀ {A B C D E}
    {k : ∫C Cᴰ [ A , B ]}{x : ∫C Cᴰ [ B , C ]}
    {y : ∫C Cᴰ [ C , D ]}{m : ∫C Cᴰ [ D , E ]}
    → (k Cᴰ.⋆ (x Cᴰ.⋆ (y Cᴰ.⋆ m))) ≡ (k Cᴰ.⋆ ((x Cᴰ.⋆ y) Cᴰ.⋆ m))
  regroup {k = k}{x}{y}{m} = cong (k Cᴰ.⋆_) (sym (Cᴰ.⋆Assoc x y m))

  α'-sec : ∀ {x y z} (xᴰ : Rᴰ.ob[ x ])(yᴰ : Rᴰ.ob[ y ])(zᴰ : Rᴰ.ob[ z ])
    → (α⁻¹ᴰ'⟨ xᴰ , yᴰ , zᴰ ⟩ Rᴰ.⋆ᴰ αᴰ'⟨ xᴰ , yᴰ , zᴰ ⟩)
        Rᴰ.≡[ M.α .nIso (x , (y , z)) .sec ] Rᴰ.idᴰ
  α'-sec xᴰ yᴰ zᴰ = Cᴰ.rectify $ Cᴰ.≡out $
      sym (R.reind-filler _ _)
    ∙ Cᴰ.⟨ sym (R.reind-filler _ _) ⟩⋆⟨ sym (R.reind-filler _ _) ⟩
    ∙ Cᴰ.⟨ Cᴰ.⟨ refl ⟩⋆⟨ regroup ∙ sym (Cᴰ.⋆Assoc _ _ _) ⟩ ⟩⋆⟨
           Cᴰ.⟨ refl ⟩⋆⟨ regroup ∙ sym (Cᴰ.⋆Assoc _ _ _) ⟩ ⟩
    ∙ conjSeq {C = ∫C Cᴰ} (Cᴰ.≡in (liftIn⋆Out (μ≅ _ _) _))
    ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ conjSeq {C = ∫C Cᴰ} (⊗R-inv (Cᴰ.≡in (liftIn⋆Out (μ≅ _ _) _)))
                       ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ Cᴰ.≡in (P.αᴰ .nIsoᴰ _ .secᴰ) ⟩⋆⟨ refl ⟩
                                     ∙ Cᴰ.⋆IdL _ ⟩
                       ∙ ⊗L-inv (Cᴰ.≡in (liftOut⋆In (μ≅ _ _) _)) ⟩⋆⟨ refl ⟩
                  ∙ Cᴰ.⋆IdL _ ⟩
    ∙ Cᴰ.≡in (liftOut⋆In (μ≅ _ _) _)
    ∙ sym Rᴰid≡

  α'-ret : ∀ {x y z} (xᴰ : Rᴰ.ob[ x ])(yᴰ : Rᴰ.ob[ y ])(zᴰ : Rᴰ.ob[ z ])
    → (αᴰ'⟨ xᴰ , yᴰ , zᴰ ⟩ Rᴰ.⋆ᴰ α⁻¹ᴰ'⟨ xᴰ , yᴰ , zᴰ ⟩)
        Rᴰ.≡[ M.α .nIso (x , (y , z)) .ret ] Rᴰ.idᴰ
  α'-ret xᴰ yᴰ zᴰ = Cᴰ.rectify $ Cᴰ.≡out $
      sym (R.reind-filler _ _)
    ∙ Cᴰ.⟨ sym (R.reind-filler _ _) ⟩⋆⟨ sym (R.reind-filler _ _) ⟩
    ∙ Cᴰ.⟨ Cᴰ.⟨ refl ⟩⋆⟨ regroup ∙ sym (Cᴰ.⋆Assoc _ _ _) ⟩ ⟩⋆⟨
           Cᴰ.⟨ refl ⟩⋆⟨ regroup ∙ sym (Cᴰ.⋆Assoc _ _ _) ⟩ ⟩
    ∙ conjSeq {C = ∫C Cᴰ} (Cᴰ.≡in (liftIn⋆Out (μ≅ _ _) _))
    ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ conjSeq {C = ∫C Cᴰ} (⊗L-inv (Cᴰ.≡in (liftIn⋆Out (μ≅ _ _) _)))
                       ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ Cᴰ.≡in (P.αᴰ .nIsoᴰ _ .retᴰ) ⟩⋆⟨ refl ⟩
                                     ∙ Cᴰ.⋆IdL _ ⟩
                       ∙ ⊗R-inv (Cᴰ.≡in (liftOut⋆In (μ≅ _ _) _)) ⟩⋆⟨ refl ⟩
                  ∙ Cᴰ.⋆IdL _ ⟩
    ∙ Cᴰ.≡in (liftOut⋆In (μ≅ _ _) _)
    ∙ sym Rᴰid≡
