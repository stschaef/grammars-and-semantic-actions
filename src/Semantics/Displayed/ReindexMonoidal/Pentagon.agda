{-# OPTIONS --lossy-unification --allow-unsolved-metas #-}
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


  -- | The pentagon.
  --
  --   Both sides collapse to `A₁ ⋆ ((A₂ ⋆ (CORE ⋆ (B₄ ⋆ B₅))) ⋆ b₃)`
  --   with
  --     A₁ = idᴰ ⊗ u⟨x,y⊗z⟩        B₄ = (v⟨w,x⟩ ⊗ idᴰ) ⊗ idᴰ
  --     A₂ = idᴰ ⊗ (idᴰ ⊗ u⟨y,z⟩)  B₅ = v⟨w⊗x,y⟩ ⊗ idᴰ
  --   and the two cores are the two sides of `P.pentagonᴰ`. Getting
  --   there is: expand the two primed associators through `⊗`, cancel
  --   the μ-lifts pairwise with `conjSeq`, and move the three
  --   associators off the primed objects with `P.αᴰ`'s naturality.
  pentagonᴰ' : ∀ {w x y z}
    (wᴰ : Rᴰ.ob[ w ])(xᴰ : Rᴰ.ob[ x ])(yᴰ : Rᴰ.ob[ y ])(zᴰ : Rᴰ.ob[ z ])
    → ((─⊗ᴰ'─ .F-homᴰ (Rᴰ.idᴰ , αᴰ'⟨ xᴰ , yᴰ , zᴰ ⟩))
        Rᴰ.⋆ᴰ (αᴰ'⟨ wᴰ , xᴰ ⊗ᴰ' yᴰ , zᴰ ⟩
        Rᴰ.⋆ᴰ (─⊗ᴰ'─ .F-homᴰ (αᴰ'⟨ wᴰ , xᴰ , yᴰ ⟩ , Rᴰ.idᴰ))))
        Rᴰ.≡[ M.pentagon w x y z ]
      (αᴰ'⟨ wᴰ , xᴰ , yᴰ ⊗ᴰ' zᴰ ⟩ Rᴰ.⋆ᴰ αᴰ'⟨ wᴰ ⊗ᴰ' xᴰ , yᴰ , zᴰ ⟩)
  pentagonᴰ' wᴰ xᴰ yᴰ zᴰ = {!!}

  -- The reduction, worked out but not yet parsed into a single chain.
  -- Reading it as `LHS ∙ ⟨P.pentagonᴰ⟩ ∙ sym RHS`:
  --
  --   LHS: strip the reinds of the two `Rᴰ` compositions and the five
  --   factors; `conjSeq` cancels v⟨w⊗(x⊗y),z⟩ then v⟨w,(x⊗y)⊗z⟩;
  --   expand `idᴰ ⊗ α'⟨x,y,z⟩` with `⊗R-seq` and `α'⟨w,x,y⟩ ⊗ idᴰ`
  --   with `⊗L-seq`; `conjSeq` cancels (idᴰ ⊗ v⟨x⊗y,z⟩) and then
  --   ((idᴰ ⊗ v⟨x,y⟩) ⊗ idᴰ); one `P.αᴰ` naturality at
  --   (idᴰ , (v⟨x,y⟩ , idᴰ)) moves α off the primed x⊗y.
  --
  --   RHS: same reind strip; `conjSeq` cancels v⟨w⊗x,y⊗z⟩; rewrite
  --   (v⟨w,x⟩ ⊗ idᴰ) ⋆ (idᴰ ⊗ u⟨y,z⟩) as (idᴰ ⊗ u⟨y,z⟩) ⋆ (v⟨w,x⟩ ⊗ idᴰ);
  --   two `P.αᴰ` naturalities, at (idᴰ , (idᴰ , u⟨y,z⟩)) and at
  --   (v⟨w,x⟩ , (idᴰ , idᴰ)), move the two associators off the primed
  --   objects. `F-idᴰ` supplies idᴰ ⊗ idᴰ ≡ idᴰ where those naturality
  --   squares need it.
  --
  -- Both land on
  --   A₁ ⋆ ((A₂ ⋆ (CORE ⋆ (B₄ ⋆ B₅))) ⋆ b₃)
  -- with A₁ = idᴰ ⊗ u⟨x,y⊗z⟩, A₂ = idᴰ ⊗ (idᴰ ⊗ u⟨y,z⟩),
  -- B₄ = (v⟨w,x⟩ ⊗ idᴰ) ⊗ idᴰ, B₅ = v⟨w⊗x,y⟩ ⊗ idᴰ, and the two cores
  -- are the two sides of `P.pentagonᴰ wᴰ xᴰ yᴰ zᴰ`.
  --
  -- The drafted chain (rejected by the parser: bracket imbalance in a
  -- 60-line mixfix expression, not a type error):
  --       -- strip the reinds of the two `Rᴰ` compositions and the five factors
  --         sym (R.reind-filler _ _)
  --       ∙ Cᴰ.⟨ sym (R.reind-filler _ _) ⟩⋆⟨ sym (R.reind-filler _ _) ⟩
  --       ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ sym (R.reind-filler _ _) ⟩⋆⟨ sym (R.reind-filler _ _) ⟩ ⟩
  --       -- T2 ⋆ T3 : cancel v⟨w⊗(x⊗y),z⟩ against u⟨w⊗(x⊗y),z⟩
  --       ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ Cᴰ.⟨ refl ⟩⋆⟨ regroup ∙ sym (Cᴰ.⋆Assoc _ _ _) ⟩ ⟩⋆⟨ refl ⟩
  --                     ∙ conjSeq {C = ∫C Cᴰ} (Cᴰ.≡in (liftIn⋆Out (μ≅ _ _) _)) ⟩
  --       -- T1 ⋆ (…) : cancel v⟨w,(x⊗y)⊗z⟩ against u⟨w,(x⊗y)⊗z⟩
  --       ∙ conjSeq {C = ∫C Cᴰ} (Cᴰ.≡in (liftIn⋆Out (μ≅ _ _) _))
  --       ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨
  --           -- F₁ = idᴰ ⊗ α'⟨x,y,z⟩, expanded through ⊗ and regrouped
  --             Cᴰ.⟨ ⟨ Rᴰid≡ ⟩⊗ₕᴰ⟨ sym (R.reind-filler _ _) ⟩
  --                ∙ ⊗R-seq _ _
  --                ∙ Cᴰ.⟨ refl ⟩⋆⟨ ⊗R-seq _ _
  --                              ∙ Cᴰ.⟨ refl ⟩⋆⟨ ⊗R-seq _ _
  --                                            ∙ Cᴰ.⟨ refl ⟩⋆⟨ ⊗R-seq _ _ ⟩ ⟩ ⟩
  --                ∙ Cᴰ.⟨ refl ⟩⋆⟨ regroup ⟩ ∙ regroup ⟩⋆⟨
  --           -- F₂ ⋆ F₃ into `l ⋆ (y ⋆ m)` shape
  --                Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⋆Assoc _ _ _ ⟩ ⟩
  --           -- cancel (idᴰ ⊗ v⟨x⊗y,z⟩) against (idᴰ ⊗ u⟨x⊗y,z⟩)
  --           ∙ conjSeq {C = ∫C Cᴰ} (⊗R-inv (Cᴰ.≡in (liftIn⋆Out (μ≅ _ _) _)))
  --           -- move α off the primed x⊗y
  --           ∙ Cᴰ.⟨ Cᴰ.⋆Assoc _ _ _
  --                ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⋆Assoc _ _ _
  --                              ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.≡in (P.αᴰ .transᴰ .N-homᴰ
  --                                    (Cᴰ.idᴰ , (liftIn (μ≅ _ _) _ , Cᴰ.idᴰ))) ⟩ ⟩
  --                ∙ Cᴰ.⟨ refl ⟩⋆⟨ regroup ⟩ ⟩⋆⟨
  --           -- F₃ = α'⟨w,x,y⟩ ⊗ idᴰ, expanded, with its head cancelled
  --                Cᴰ.⟨ refl ⟩⋆⟨ ⟨ sym (R.reind-filler _ _) ⟩⊗ₕᴰ⟨ Rᴰid≡ ⟩
  --                            ∙ ⊗L-seq _ _
  --                            ∙ Cᴰ.⟨ refl ⟩⋆⟨ ⊗L-seq _ _
  --                                          ∙ Cᴰ.⟨ refl ⟩⋆⟨ ⊗L-seq _ _
  --                                                        ∙ Cᴰ.⟨ refl ⟩⋆⟨ ⊗L-seq _ _ ⟩ ⟩ ⟩
  --                ∙ ⋆cancelL {C = ∫C Cᴰ} (⊗L-inv (Cᴰ.≡in (liftIn⋆Out (μ≅ _ _) _))) ⟩
  --           -- cancel ((idᴰ ⊗ v⟨x,y⟩) ⊗ idᴰ) against ((idᴰ ⊗ u⟨x,y⟩) ⊗ idᴰ)
  --           ∙ conjSeq {C = ∫C Cᴰ} (⊗L-inv (⊗R-inv (Cᴰ.≡in (liftIn⋆Out (μ≅ _ _) _))))
  --           ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ Cᴰ.⋆Assoc _ _ _ ⟩⋆⟨ refl ⟩ ⟩
  --         ⟩⋆⟨ refl ⟩ ⟩
  --       ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ Cᴰ.≡in (P.pentagonᴰ _ _ _ _) ⟩⋆⟨ refl ⟩ ⟩ ⟩⋆⟨ refl ⟩ ⟩
  --       ∙ sym
  --         ( sym (R.reind-filler _ _)
  --         ∙ Cᴰ.⟨ sym (R.reind-filler _ _) ⟩⋆⟨ sym (R.reind-filler _ _) ⟩
  --         ∙ Cᴰ.⟨ Cᴰ.⟨ refl ⟩⋆⟨ regroup ∙ sym (Cᴰ.⋆Assoc _ _ _) ⟩ ⟩⋆⟨
  --                Cᴰ.⟨ refl ⟩⋆⟨ regroup ∙ sym (Cᴰ.⋆Assoc _ _ _) ⟩ ⟩
  --         ∙ conjSeq {C = ∫C Cᴰ} (Cᴰ.≡in (liftIn⋆Out (μ≅ _ _) _))
  --         ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨
  --               Cᴰ.⋆Assoc _ _ _
  --             ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⋆Assoc _ _ _
  --                           ∙ Cᴰ.⟨ sym (Cᴰ.≡in (P.─⊗ᴰ─ .F-seqᴰ _ _))
  --                                ∙ ⟨ Cᴰ.⋆IdR _ ∙ sym (Cᴰ.⋆IdL _) ⟩⊗ₕᴰ⟨
  --                                    Cᴰ.⋆IdL _ ∙ sym (Cᴰ.⋆IdR _) ⟩
  --                                ∙ Cᴰ.≡in (P.─⊗ᴰ─ .F-seqᴰ _ _) ⟩⋆⟨ refl ⟩
  --                           ∙ Cᴰ.⋆Assoc _ _ _ ⟩
  --             ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ ⟨ refl ⟩⊗ₕᴰ⟨ sym (Cᴰ.≡in (P.─⊗ᴰ─ .F-idᴰ)) ⟩
  --                                ∙ Cᴰ.≡in (P.αᴰ .transᴰ .N-homᴰ
  --                                    (Cᴰ.idᴰ , (Cᴰ.idᴰ , liftOut (μ≅ _ _) _))) ⟩⋆⟨ refl ⟩ ⟩
  --             ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⋆Assoc _ _ _
  --                           ∙ Cᴰ.⟨ refl ⟩⋆⟨ sym (Cᴰ.⋆Assoc _ _ _)
  --                                         ∙ Cᴰ.⟨ ⟨ refl ⟩⊗ₕᴰ⟨ sym (Cᴰ.≡in (P.─⊗ᴰ─ .F-idᴰ)) ⟩
  --                                              ∙ Cᴰ.≡in (P.αᴰ .transᴰ .N-homᴰ
  --                                                  (liftIn (μ≅ _ _) _ , (Cᴰ.idᴰ , Cᴰ.idᴰ))) ⟩⋆⟨ refl ⟩
  --                                         ∙ Cᴰ.⋆Assoc _ _ _ ⟩ ⟩
  --             ∙ sym (Cᴰ.⋆Assoc _ _ _)
  --             ∙ Cᴰ.⟨ sym (Cᴰ.⋆Assoc _ _ _) ⟩⋆⟨ refl ⟩
  --             ⟩⋆⟨ refl ⟩ ⟩)
