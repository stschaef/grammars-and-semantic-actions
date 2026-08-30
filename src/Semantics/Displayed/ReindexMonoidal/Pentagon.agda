{-# OPTIONS --lossy-unification #-}
{- The pentagon coherence for the reindexed monoidal structure.
   Both sides reduce to `PRE ⋆ (CORE ⋆ SUF)` with the same prefix and
   suffix; the cores are the two sides of `P.pentagonᴰ`.
-}
module Semantics.Displayed.ReindexMonoidal.Pentagon where

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
open import Semantics.Displayed.ReindexMonoidal.Assoc

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

module Pentagon {M : MonoidalCategory ℓM ℓM'} {N : MonoidalCategory ℓN ℓN'}
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

  open Assoc P G cartLifts public
  open IsoLifts Cᴰ cartLifts

  -- | `idᴰ ⊗ (A ⋆ B)` splits.
  ⊗R-seq : ∀ {a b c d}{f : N.C [ b , c ]}{g : N.C [ c , d ]}
    {aᴰ : Cᴰ.ob[ a ]}{bᴰ : Cᴰ.ob[ b ]}{cᴰ : Cᴰ.ob[ c ]}{dᴰ : Cᴰ.ob[ d ]}
    (A : Cᴰ.Hom[ f ][ bᴰ , cᴰ ])(B : Cᴰ.Hom[ g ][ cᴰ , dᴰ ])
    → Path Cᴰ.Hom[ (a N.⊗ b , aᴰ P.⊗ᴰ bᴰ) , (a N.⊗ d , aᴰ P.⊗ᴰ dᴰ) ]
        (_ , Cᴰ.idᴰ {p = aᴰ} P.⊗ₕᴰ (A Cᴰ.⋆ᴰ B))
        (_ , (Cᴰ.idᴰ {p = aᴰ} P.⊗ₕᴰ A) Cᴰ.⋆ᴰ (Cᴰ.idᴰ {p = aᴰ} P.⊗ₕᴰ B))
  ⊗R-seq A B = ⟨ sym (Cᴰ.⋆IdL _) ⟩⊗ₕᴰ⟨ refl ⟩ ∙ Cᴰ.≡in (P.─⊗ᴰ─ .F-seqᴰ _ _)

  -- | `(A ⋆ B) ⊗ idᴰ` splits.
  ⊗L-seq : ∀ {a b c d}{f : N.C [ b , c ]}{g : N.C [ c , d ]}
    {aᴰ : Cᴰ.ob[ a ]}{bᴰ : Cᴰ.ob[ b ]}{cᴰ : Cᴰ.ob[ c ]}{dᴰ : Cᴰ.ob[ d ]}
    (A : Cᴰ.Hom[ f ][ bᴰ , cᴰ ])(B : Cᴰ.Hom[ g ][ cᴰ , dᴰ ])
    → Path Cᴰ.Hom[ (b N.⊗ a , bᴰ P.⊗ᴰ aᴰ) , (d N.⊗ a , dᴰ P.⊗ᴰ aᴰ) ]
        (_ , (A Cᴰ.⋆ᴰ B) P.⊗ₕᴰ Cᴰ.idᴰ {p = aᴰ})
        (_ , (A P.⊗ₕᴰ Cᴰ.idᴰ {p = aᴰ}) Cᴰ.⋆ᴰ (B P.⊗ₕᴰ Cᴰ.idᴰ {p = aᴰ}))
  ⊗L-seq A B = ⟨ refl ⟩⊗ₕᴰ⟨ sym (Cᴰ.⋆IdL _) ⟩ ∙ Cᴰ.≡in (P.─⊗ᴰ─ .F-seqᴰ _ _)



  -- | The heart of the pentagon: with the outer μ-lifts stripped by
  --   `conjSeq`, the two sides of the pentagon have these cores.
  pentCore : ∀ {w x y z}
    (wᴰ : Rᴰ.ob[ w ])(xᴰ : Rᴰ.ob[ x ])(yᴰ : Rᴰ.ob[ y ])(zᴰ : Rᴰ.ob[ z ])
    → Path Cᴰ.Hom[ ((G.F ⟅ w ⟆) N.⊗ (G.F ⟅ x M.⊗ (y M.⊗ z) ⟆)
                   , wᴰ P.⊗ᴰ (xᴰ ⊗ᴰ' (yᴰ ⊗ᴰ' zᴰ)))
                 , ((G.F ⟅ (w M.⊗ x) M.⊗ y ⟆) N.⊗ (G.F ⟅ z ⟆)
                   , ((wᴰ ⊗ᴰ' xᴰ) ⊗ᴰ' yᴰ) P.⊗ᴰ zᴰ) ]
        (_ , (Rᴰ.idᴰ P.⊗ₕᴰ αᴰ'⟨ xᴰ , yᴰ , zᴰ ⟩)
             Cᴰ.⋆ᴰ (((Cᴰ.idᴰ P.⊗ₕᴰ liftOut (μ≅ (x M.⊗ y) z) ((xᴰ ⊗ᴰ' yᴰ) P.⊗ᴰ zᴰ))
                     Cᴰ.⋆ᴰ (P.αᴰ⟨ wᴰ , xᴰ ⊗ᴰ' yᴰ , zᴰ ⟩
                     Cᴰ.⋆ᴰ (liftIn (μ≅ w (x M.⊗ y)) (wᴰ P.⊗ᴰ (xᴰ ⊗ᴰ' yᴰ)) P.⊗ₕᴰ Cᴰ.idᴰ)))
                    Cᴰ.⋆ᴰ (αᴰ'⟨ wᴰ , xᴰ , yᴰ ⟩ P.⊗ₕᴰ Rᴰ.idᴰ)))
        (_ , ((Cᴰ.idᴰ P.⊗ₕᴰ liftOut (μ≅ x (y M.⊗ z)) (xᴰ P.⊗ᴰ (yᴰ ⊗ᴰ' zᴰ)))
              Cᴰ.⋆ᴰ (P.αᴰ⟨ wᴰ , xᴰ , yᴰ ⊗ᴰ' zᴰ ⟩
              Cᴰ.⋆ᴰ (liftIn (μ≅ w x) (wᴰ P.⊗ᴰ xᴰ) P.⊗ₕᴰ Cᴰ.idᴰ)))
             Cᴰ.⋆ᴰ ((Cᴰ.idᴰ P.⊗ₕᴰ liftOut (μ≅ y z) (yᴰ P.⊗ᴰ zᴰ))
              Cᴰ.⋆ᴰ (P.αᴰ⟨ wᴰ ⊗ᴰ' xᴰ , yᴰ , zᴰ ⟩
              Cᴰ.⋆ᴰ (liftIn (μ≅ (w M.⊗ x) y) ((wᴰ ⊗ᴰ' xᴰ) P.⊗ᴰ yᴰ) P.⊗ₕᴰ Cᴰ.idᴰ))))
  pentCore wᴰ xᴰ yᴰ zᴰ =
    -- expand F₁ = Rᴰ.idᴰ ⊗ α'⟨x,y,z⟩ into a five-fold composite, regrouped
      Cᴰ.⟨ ⟨ Rᴰid≡ ⟩⊗ₕᴰ⟨ sym (R.reind-filler _ _) ⟩
         ∙ ⊗R-seq _ _
         ∙ Cᴰ.⟨ refl ⟩⋆⟨ ⊗R-seq _ _
                       ∙ Cᴰ.⟨ refl ⟩⋆⟨ ⊗R-seq _ _
                                     ∙ Cᴰ.⟨ refl ⟩⋆⟨ ⊗R-seq _ _ ⟩ ⟩ ⟩
         ∙ Cᴰ.⟨ refl ⟩⋆⟨ regroup ⟩
         ∙ regroup ⟩⋆⟨ refl ⟩
    -- reshape F₂ ⋆ F₃ into conjugate form
    ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⋆Assoc _ _ _ ⟩ ⟩
    -- cancel (idᴰ ⊗ v⟨x⊗y,z⟩) against (idᴰ ⊗ u⟨x⊗y,z⟩)
    ∙ conjSeq {C = ∫C Cᴰ} (⊗R-inv (Cᴰ.≡in (liftIn⋆Out (μ≅ _ _) _)))
    -- move α off the primed x⊗y with P.αᴰ naturality
    ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨
          Cᴰ.⋆Assoc _ _ _
        ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⋆Assoc _ _ _ ⟩
        ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.≡in (P.αᴰ .transᴰ .N-homᴰ
                (Cᴰ.idᴰ , (liftIn (μ≅ _ _) _ , Cᴰ.idᴰ))) ⟩ ⟩
        ∙ regroup ⟩⋆⟨ refl ⟩ ⟩
    -- expand F₃ = α'⟨w,x,y⟩ ⊗ idᴰ and cancel its head against (v⟨w,x⊗y⟩ ⊗ idᴰ)
    ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ refl ⟩⋆⟨
            Cᴰ.⟨ refl ⟩⋆⟨ ⟨ sym (R.reind-filler _ _) ⟩⊗ₕᴰ⟨ Rᴰid≡ ⟩
                        ∙ ⊗L-seq _ _
                        ∙ Cᴰ.⟨ refl ⟩⋆⟨ ⊗L-seq _ _
                                      ∙ Cᴰ.⟨ refl ⟩⋆⟨ ⊗L-seq _ _
                                                    ∙ Cᴰ.⟨ refl ⟩⋆⟨ ⊗L-seq _ _ ⟩ ⟩ ⟩ ⟩
          ∙ ⋆cancelL {C = ∫C Cᴰ} (⊗L-inv (Cᴰ.≡in (liftIn⋆Out (μ≅ _ _) _))) ⟩ ⟩
    -- cancel ((idᴰ ⊗ v⟨x,y⟩) ⊗ idᴰ) against ((idᴰ ⊗ u⟨x,y⟩) ⊗ idᴰ)
    ∙ Cᴰ.⟨ refl ⟩⋆⟨
        conjSeq {C = ∫C Cᴰ} (⊗L-inv (⊗R-inv (Cᴰ.≡in (liftIn⋆Out (μ≅ _ _) _)))) ⟩
    -- the core is now exactly P.pentagonᴰ's left-hand side
    ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ Cᴰ.⋆Assoc _ _ _ ⟩⋆⟨ refl ⟩ ⟩ ⟩
    ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ refl ⟩⋆⟨
        Cᴰ.⟨ Cᴰ.≡in (P.pentagonᴰ _ _ _ _) ⟩⋆⟨ refl ⟩ ⟩ ⟩
    ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⋆Assoc _ _ _ ⟩ ⟩
    -- the right-hand core, reduced to the same normal form
    ∙ sym
      ( Cᴰ.⋆Assoc _ _ _
      ∙ Cᴰ.⟨ refl ⟩⋆⟨
            Cᴰ.⋆Assoc _ _ _
          ∙ Cᴰ.⟨ refl ⟩⋆⟨ sym (Cᴰ.⋆Assoc _ _ _) ⟩
          -- (v⟨w,x⟩ ⊗ idᴰ) and (idᴰ ⊗ u⟨y,z⟩) act on different factors
          ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ sym (Cᴰ.≡in (P.─⊗ᴰ─ .F-seqᴰ _ _))
                             ∙ ⟨ Cᴰ.⋆IdR _ ∙ sym (Cᴰ.⋆IdL _) ⟩⊗ₕᴰ⟨
                                 Cᴰ.⋆IdL _ ∙ sym (Cᴰ.⋆IdR _) ⟩
                             ∙ Cᴰ.≡in (P.─⊗ᴰ─ .F-seqᴰ _ _) ⟩⋆⟨ refl ⟩ ⟩
          ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⋆Assoc _ _ _ ⟩
          ∙ sym (Cᴰ.⋆Assoc _ _ _) ⟩
      -- move α off the primed y⊗z
      ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨
              Cᴰ.⟨ refl ⟩⋆⟨ ⟨ sym (Cᴰ.≡in (P.─⊗ᴰ─ .F-idᴰ)) ⟩⊗ₕᴰ⟨ refl ⟩ ⟩
            ∙ sym (Cᴰ.≡in (P.αᴰ .transᴰ .N-homᴰ
                (Cᴰ.idᴰ , (Cᴰ.idᴰ , liftOut (μ≅ _ _) _)))) ⟩⋆⟨ refl ⟩ ⟩
      ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⋆Assoc _ _ _ ⟩
      -- move α off the primed w⊗x
      ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ refl ⟩⋆⟨
              sym (Cᴰ.⋆Assoc _ _ _)
            ∙ Cᴰ.⟨ Cᴰ.⟨ ⟨ refl ⟩⊗ₕᴰ⟨ sym (Cᴰ.≡in (P.─⊗ᴰ─ .F-idᴰ)) ⟩ ⟩⋆⟨ refl ⟩
                 ∙ Cᴰ.≡in (P.αᴰ .transᴰ .N-homᴰ
                     (liftIn (μ≅ _ _) _ , (Cᴰ.idᴰ , Cᴰ.idᴰ))) ⟩⋆⟨ refl ⟩
            ∙ Cᴰ.⋆Assoc _ _ _ ⟩ ⟩ ⟩ )

  pentagonᴰ' : ∀ {w x y z}
    (wᴰ : Rᴰ.ob[ w ])(xᴰ : Rᴰ.ob[ x ])(yᴰ : Rᴰ.ob[ y ])(zᴰ : Rᴰ.ob[ z ])
    → ((─⊗ᴰ'─ .F-homᴰ (Rᴰ.idᴰ , αᴰ'⟨ xᴰ , yᴰ , zᴰ ⟩))
        Rᴰ.⋆ᴰ (αᴰ'⟨ wᴰ , xᴰ ⊗ᴰ' yᴰ , zᴰ ⟩
        Rᴰ.⋆ᴰ (─⊗ᴰ'─ .F-homᴰ (αᴰ'⟨ wᴰ , xᴰ , yᴰ ⟩ , Rᴰ.idᴰ))))
        Rᴰ.≡[ M.pentagon w x y z ]
      (αᴰ'⟨ wᴰ , xᴰ , yᴰ ⊗ᴰ' zᴰ ⟩ Rᴰ.⋆ᴰ αᴰ'⟨ wᴰ ⊗ᴰ' xᴰ , yᴰ , zᴰ ⟩)
  pentagonᴰ' wᴰ xᴰ yᴰ zᴰ = Cᴰ.rectify $ Cᴰ.≡out $
      sym (R.reind-filler _ _)
    ∙ Cᴰ.⟨ sym (R.reind-filler _ _) ⟩⋆⟨ sym (R.reind-filler _ _) ⟩
    ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ sym (R.reind-filler _ _) ⟩⋆⟨ sym (R.reind-filler _ _) ⟩ ⟩
    ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ Cᴰ.⟨ refl ⟩⋆⟨ regroup ∙ sym (Cᴰ.⋆Assoc _ _ _) ⟩ ⟩⋆⟨ refl ⟩
                  ∙ conjSeq {C = ∫C Cᴰ} (Cᴰ.≡in (liftIn⋆Out (μ≅ _ _) _)) ⟩
    ∙ conjSeq {C = ∫C Cᴰ} (Cᴰ.≡in (liftIn⋆Out (μ≅ _ _) _))
    ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ pentCore wᴰ xᴰ yᴰ zᴰ ⟩⋆⟨ refl ⟩ ⟩
    ∙ sym
      ( sym (R.reind-filler _ _)
      ∙ Cᴰ.⟨ sym (R.reind-filler _ _) ⟩⋆⟨ sym (R.reind-filler _ _) ⟩
      ∙ Cᴰ.⟨ Cᴰ.⟨ refl ⟩⋆⟨ regroup ∙ sym (Cᴰ.⋆Assoc _ _ _) ⟩ ⟩⋆⟨
             Cᴰ.⟨ refl ⟩⋆⟨ regroup ∙ sym (Cᴰ.⋆Assoc _ _ _) ⟩ ⟩
      ∙ conjSeq {C = ∫C Cᴰ} (Cᴰ.≡in (liftIn⋆Out (μ≅ _ _) _)) )
