{-# OPTIONS --lossy-unification #-}
{- Reindexing a displayed monoidal structure along a strong monoidal
   functor, without `hasPropHoms`.

   ccl's `Displayed.Instances.Reindex.Monoidal` builds this only when
   the displayed category has propositional homs, which makes
   functoriality, naturality, and the pentagon/triangle coherences
   free. A proof-relevant gluing model does not have propositional
   homs, so those all have to be discharged.

   The base-level path computations are ccl's; the displayed proofs
   are the new content. Where ccl needs only a `WeakIsoLift`, we need
   a genuine displayed iso, which `Semantics.Displayed.IsoLift`
   extracts from a cartesian lift.
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

private
  variable
    ℓM ℓM' ℓN ℓN' ℓCᴰ ℓCᴰ' : Level

-- | Six-fold reassociation: conjugating by an iso pair is functorial.
--   `u ⋆ (x ⋆ ((v ⋆ u) ⋆ (y ⋆ v)))  ≡  (u ⋆ (x ⋆ v)) ⋆ (u ⋆ (y ⋆ v))`
module _ {C : Category ℓM ℓM'} where
  private module C = Category C
  conjReassoc : ∀ {a b c d e f g}
    (u : C [ a , b ])(x : C [ b , c ])(v : C [ c , d ])
    (u' : C [ d , e ])(y : C [ e , f ])(v' : C [ f , g ])
    → (u C.⋆ (x C.⋆ ((v C.⋆ u') C.⋆ (y C.⋆ v'))))
      ≡ ((u C.⋆ (x C.⋆ v)) C.⋆ (u' C.⋆ (y C.⋆ v')))
  conjReassoc u x v u' y v' =
      cong (u C.⋆_) (cong (x C.⋆_) (C.⋆Assoc v u' (y C.⋆ v')))
    ∙ cong (u C.⋆_) (sym (C.⋆Assoc x v (u' C.⋆ (y C.⋆ v'))))
    ∙ sym (C.⋆Assoc u (x C.⋆ v) (u' C.⋆ (y C.⋆ v')))

open Functor
open Functorᴰ
open NatTrans
open isIso
open NatIso
open NatIsoᴰ
open NatTransᴰ
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

  open IsoLifts Cᴰ cartLifts

  private
    -- The base isos we transport along: `ε` for the unit and `μ` for
    -- the tensor, both inverted, since a cartesian lift moves an
    -- object *backwards* along a base map.
    ε≅ : CatIso N.C (G.F ⟅ M.unit ⟆) N.unit
    ε≅ = invIso G.ε-Iso

    μ≅ : ∀ x y → CatIso N.C (G.F ⟅ x M.⊗ y ⟆) ((G.F ⟅ x ⟆) N.⊗ (G.F ⟅ y ⟆))
    μ≅ x y = invIso (NatIsoAt G.μ-Iso (x , y))

  -- | `Rᴰ`'s identity is `Cᴰ`'s, reindexed along `G`'s unit law.
  Rᴰid≡ : ∀ {x} {xᴰ : Cᴰ.ob[ G.F ⟅ x ⟆ ]}
    → Path Cᴰ.Hom[ (G.F ⟅ x ⟆ , xᴰ) , (G.F ⟅ x ⟆ , xᴰ) ]
        (G.F ⟪ M.id ⟫ , Rᴰ.idᴰ) (N.id , Cᴰ.idᴰ)
  Rᴰid≡ = sym (R.reind-filler (sym G.F-id) Cᴰ.idᴰ)

  -- | Congruence for the displayed tensor of morphisms.
  ⟨_⟩⊗ₕᴰ⟨_⟩ : ∀ {x y z w}{xᴰ : Cᴰ.ob[ x ]}{yᴰ : Cᴰ.ob[ y ]}
    {zᴰ : Cᴰ.ob[ z ]}{wᴰ : Cᴰ.ob[ w ]}
    {f f' : N.C [ x , y ]}{fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ]}{fᴰ' : Cᴰ.Hom[ f' ][ xᴰ , yᴰ ]}
    {g g' : N.C [ z , w ]}{gᴰ : Cᴰ.Hom[ g ][ zᴰ , wᴰ ]}{gᴰ' : Cᴰ.Hom[ g' ][ zᴰ , wᴰ ]}
    → Path Cᴰ.Hom[ (x , xᴰ) , (y , yᴰ) ] (f , fᴰ) (f' , fᴰ')
    → Path Cᴰ.Hom[ (z , zᴰ) , (w , wᴰ) ] (g , gᴰ) (g' , gᴰ')
    → Path Cᴰ.Hom[ (x N.⊗ z , xᴰ P.⊗ᴰ zᴰ) , (y N.⊗ w , yᴰ P.⊗ᴰ wᴰ) ]
        (f N.⊗ₕ g , fᴰ P.⊗ₕᴰ gᴰ) (f' N.⊗ₕ g' , fᴰ' P.⊗ₕᴰ gᴰ')
  ⟨ p ⟩⊗ₕᴰ⟨ q ⟩ i = (p i .fst N.⊗ₕ q i .fst) , (p i .snd P.⊗ₕᴰ q i .snd)

  unitᴰ' : Rᴰ.ob[ M.unit ]
  unitᴰ' = liftOb ε≅ P.unitᴰ

  _⊗ᴰ'_ : ∀ {x y} → Rᴰ.ob[ x ] → Rᴰ.ob[ y ] → Rᴰ.ob[ x M.⊗ y ]
  _⊗ᴰ'_ {x} {y} xᴰ yᴰ = liftOb (μ≅ x y) (xᴰ P.⊗ᴰ yᴰ)

  ─⊗ᴰ'─ : Functorᴰ M.─⊗─ (Rᴰ ×Cᴰ Rᴰ) Rᴰ
  ─⊗ᴰ'─ .F-obᴰ (xᴰ , yᴰ) = xᴰ ⊗ᴰ' yᴰ
  ─⊗ᴰ'─ .F-homᴰ {f = f , g} (fᴰ , gᴰ) = R.reind
    (cong₂ N._⋆_ refl (G.μ .N-hom _) ∙ sym (N.⋆Assoc _ _ _)
      ∙ cong₂ N._⋆_ (G.μ-isIso _ .sec) refl ∙ N.⋆IdL _)
    (liftOut (μ≅ _ _) _ Cᴰ.⋆ᴰ ((fᴰ P.⊗ₕᴰ gᴰ) Cᴰ.⋆ᴰ liftIn (μ≅ _ _) _))
  ─⊗ᴰ'─ .F-idᴰ = Cᴰ.rectify $ Cᴰ.≡out $
    sym (R.reind-filler _ _)
    ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ ⟨ Rᴰid≡ ⟩⊗ₕᴰ⟨ Rᴰid≡ ⟩ ∙ Cᴰ.≡in (P.─⊗ᴰ─ .F-idᴰ) ⟩⋆⟨ refl ⟩
                   ∙ Cᴰ.⋆IdL _ ⟩
    ∙ Cᴰ.≡in (liftOut⋆In _ _)
    ∙ sym Rᴰid≡
  ─⊗ᴰ'─ .F-seqᴰ (fᴰ , gᴰ) (f'ᴰ , g'ᴰ) = Cᴰ.rectify $ Cᴰ.≡out $
      sym (R.reind-filler _ _)
    ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ ⟨ sym (R.reind-filler _ _) ⟩⊗ₕᴰ⟨ sym (R.reind-filler _ _) ⟩
                         ∙ Cᴰ.≡in (P.─⊗ᴰ─ .F-seqᴰ _ _) ⟩⋆⟨ refl ⟩ ⟩
    ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⋆Assoc _ _ _ ⟩
    ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ refl ⟩⋆⟨ sym (Cᴰ.⋆IdL _)
                    ∙ Cᴰ.⟨ sym (Cᴰ.≡in (liftIn⋆Out _ _)) ⟩⋆⟨ refl ⟩ ⟩ ⟩
    ∙ conjReassoc {C = ∫C Cᴰ} _ _ _ _ _ _
    ∙ Cᴰ.⟨ R.reind-filler _ _ ⟩⋆⟨ R.reind-filler _ _ ⟩
    ∙ R.reind-filler _ _

  tenstrᴰ' : TensorStrᴰ M Rᴰ
  tenstrᴰ' .TensorStrᴰ.─⊗ᴰ─ = ─⊗ᴰ'─
  tenstrᴰ' .TensorStrᴰ.unitᴰ = unitᴰ'

------------------------------------------------------------------------
-- The structure maps
--
-- Objects and base-level paths are ccl's (`Reindex.Monoidal`); only
-- the `WeakIsoLift`s are replaced by genuine displayed isos.
------------------------------------------------------------------------

  αᴰ'⟨_,_,_⟩ : ∀ {x y z} (xᴰ : Rᴰ.ob[ x ])(yᴰ : Rᴰ.ob[ y ])(zᴰ : Rᴰ.ob[ z ])
    → Rᴰ.Hom[ M.α⟨ x , y , z ⟩ ][ xᴰ ⊗ᴰ' (yᴰ ⊗ᴰ' zᴰ) , (xᴰ ⊗ᴰ' yᴰ) ⊗ᴰ' zᴰ ]
  αᴰ'⟨ p , q , r ⟩ = R.reind
    (cong₂ N._⋆_ refl
      (cong₂ N._⋆_ refl (sym (N.⋆Assoc _ _ _) ∙ (G.αμ-law _ _ _)))
    ∙ sym (N.⋆Assoc _ _ _) ∙ sym (N.⋆Assoc _ _ _)
    ∙ cong₂ N._⋆_
       (N.⋆Assoc _ _ _
       ∙ cong₂ N._⋆_ refl
         (sym (N.⋆Assoc _ _ _)
         ∙ cong₂ N._⋆_
           (F-Iso {F = N.─⊗─}
             (CatIso× N.C N.C idCatIso (NatIsoAt G.μ-Iso _))
             .snd .sec)
           refl
         ∙ N.⋆IdL _)
       ∙ G.μ-isIso _ .sec)
       refl
    ∙ N.⋆IdL _)
    (liftOut (μ≅ _ _) _
    Cᴰ.⋆ᴰ (Cᴰ.idᴰ P.⊗ₕᴰ liftOut (μ≅ _ _) _)
    Cᴰ.⋆ᴰ P.αᴰ⟨ p , q , r ⟩
    Cᴰ.⋆ᴰ (liftIn (μ≅ _ _) _ P.⊗ₕᴰ Cᴰ.idᴰ)
    Cᴰ.⋆ᴰ liftIn (μ≅ _ _) _)

  α⁻¹ᴰ'⟨_,_,_⟩ : ∀ {x y z} (xᴰ : Rᴰ.ob[ x ])(yᴰ : Rᴰ.ob[ y ])(zᴰ : Rᴰ.ob[ z ])
    → Rᴰ.Hom[ M.α⁻¹⟨ x , y , z ⟩ ][ (xᴰ ⊗ᴰ' yᴰ) ⊗ᴰ' zᴰ , xᴰ ⊗ᴰ' (yᴰ ⊗ᴰ' zᴰ) ]
  α⁻¹ᴰ'⟨ p , q , r ⟩ = R.reind
    (⋆CancelR (F-Iso {F = G.F} (NatIsoAt M.α _))
      ((N.⋆Assoc _ _ _)
      ∙ cong₂ N._⋆_ refl
        (N.⋆Assoc _ _ _
        ∙ cong₂ N._⋆_ refl
          (N.⋆Assoc _ _ _
          ∙ cong₂ N._⋆_ refl (sym (G.αμ-law _ _ _))
          ∙ sym (N.⋆Assoc _ _ _)
          ∙ cong₂ N._⋆_
            (sym (N.⋆Assoc _ _ _) ∙ cong₂ N._⋆_ (N.α .nIso _ .sec) refl
            ∙ N.⋆IdL _)
            refl)
        ∙ sym (N.⋆Assoc _ _ _)
        ∙ cong₂ N._⋆_
            (F-Iso {F = N.─⊗─}
              (CatIso× N.C N.C (NatIsoAt G.μ-Iso _) idCatIso) .snd .sec)
            refl
        ∙ N.⋆IdL _)
      ∙ G.μ-isIso _ .sec
      ∙ sym ((F-Iso {F = G.F} (NatIsoAt M.α _)) .snd .sec)))
    (liftOut (μ≅ _ _) _
    Cᴰ.⋆ᴰ (liftOut (μ≅ _ _) _ P.⊗ₕᴰ Cᴰ.idᴰ)
    Cᴰ.⋆ᴰ P.α⁻¹ᴰ⟨ p , q , r ⟩
    Cᴰ.⋆ᴰ (Cᴰ.idᴰ P.⊗ₕᴰ liftIn (μ≅ _ _) _)
    Cᴰ.⋆ᴰ liftIn (μ≅ _ _) _)

  ηᴰ'⟨_⟩ : ∀ {x} (xᴰ : Rᴰ.ob[ x ]) → Rᴰ.Hom[ M.η⟨ x ⟩ ][ unitᴰ' ⊗ᴰ' xᴰ , xᴰ ]
  ηᴰ'⟨ p ⟩ = R.reind
    (cong₂ N._⋆_ refl
      (cong₂ N._⋆_ refl (sym (G.ηε-law _))
      ∙ sym (N.⋆Assoc _ _ _)
      ∙ cong₂ N._⋆_
        (sym (N.⋆Assoc _ _ _)
        ∙ cong₂ N._⋆_
          (F-Iso {F = N.─⊗─} (CatIso× N.C N.C G.ε-Iso idCatIso) .snd .sec)
          refl
        ∙ N.⋆IdL _)
        refl)
    ∙ sym (N.⋆Assoc _ _ _)
    ∙ cong₂ N._⋆_ (NatIsoAt G.μ-Iso _ .snd .sec) refl
    ∙ N.⋆IdL _)
    (liftOut (μ≅ _ _) _ Cᴰ.⋆ᴰ ((liftOut ε≅ _ P.⊗ₕᴰ Cᴰ.idᴰ) Cᴰ.⋆ᴰ P.ηᴰ⟨ _ ⟩))

  η⁻¹ᴰ'⟨_⟩ : ∀ {x} (xᴰ : Rᴰ.ob[ x ]) → Rᴰ.Hom[ M.η⁻¹⟨ x ⟩ ][ xᴰ , unitᴰ' ⊗ᴰ' xᴰ ]
  η⁻¹ᴰ'⟨ p ⟩ = R.reind
    (G.η⁻ε-law _)
    ((P.η⁻¹ᴰ⟨ _ ⟩ Cᴰ.⋆ᴰ (liftIn ε≅ _ P.⊗ₕᴰ Cᴰ.idᴰ)) Cᴰ.⋆ᴰ liftIn (μ≅ _ _) _)

  ρᴰ'⟨_⟩ : ∀ {x} (xᴰ : Rᴰ.ob[ x ]) → Rᴰ.Hom[ M.ρ⟨ x ⟩ ][ xᴰ ⊗ᴰ' unitᴰ' , xᴰ ]
  ρᴰ'⟨ p ⟩ = R.reind
    (cong₂ N._⋆_ refl
    (cong₂ N._⋆_ refl (sym (G.ρε-law _))
    ∙ sym (N.⋆Assoc _ _ _)
    ∙ cong₂ N._⋆_
      (sym (N.⋆Assoc _ _ _)
      ∙ cong₂ N._⋆_
        (F-Iso {F = N.─⊗─} (CatIso× N.C N.C idCatIso G.ε-Iso) .snd .sec)
        refl
      ∙ N.⋆IdL _)
      refl)
    ∙ sym (N.⋆Assoc _ _ _)
    ∙ cong₂ N._⋆_ (G.μ-isIso _ .sec) refl
    ∙ N.⋆IdL _)
    (liftOut (μ≅ _ _) _
    Cᴰ.⋆ᴰ (Cᴰ.idᴰ P.⊗ₕᴰ liftOut ε≅ _)
    Cᴰ.⋆ᴰ P.ρᴰ⟨ p ⟩)

  ρ⁻¹ᴰ'⟨_⟩ : ∀ {x} (xᴰ : Rᴰ.ob[ x ]) → Rᴰ.Hom[ M.ρ⁻¹⟨ x ⟩ ][ xᴰ , xᴰ ⊗ᴰ' unitᴰ' ]
  ρ⁻¹ᴰ'⟨ p ⟩ = R.reind
    (⋆CancelR (F-Iso {F = G.F} (NatIsoAt M.ρ _))
      (N.⋆Assoc _ _ _ ∙ cong₂ N._⋆_ refl (G.ρε-law _)
      ∙ N.ρ .nIso _ .sec
      ∙ sym (F-Iso {F = G.F} (NatIsoAt M.ρ _) .snd .sec)))
    (P.ρ⁻¹ᴰ⟨ p ⟩
      Cᴰ.⋆ᴰ (Cᴰ.idᴰ P.⊗ₕᴰ liftIn ε≅ _)
      Cᴰ.⋆ᴰ liftIn (μ≅ _ _) _)

------------------------------------------------------------------------
-- Coherence
------------------------------------------------------------------------

  private
    -- `idᴰ ⋆ᴰ Rᴰ.idᴰ` is `idᴰ`.
    id⋆Rid : ∀ {x}{xᴰ : Cᴰ.ob[ G.F ⟅ x ⟆ ]}
      → Path Cᴰ.Hom[ (G.F ⟅ x ⟆ , xᴰ) , (G.F ⟅ x ⟆ , xᴰ) ]
          (_ , Cᴰ.idᴰ Cᴰ.⋆ᴰ Rᴰ.idᴰ) (N.id , Cᴰ.idᴰ)
    id⋆Rid = Cᴰ.⟨ refl ⟩⋆⟨ Rᴰid≡ ⟩ ∙ Cᴰ.⋆IdL _

    -- Precomposing `ρᴰ'` with the μ-lift cancels its leading projection.
    v⋆ρ' : ∀ {x} (xᴰ : Rᴰ.ob[ x ])
      → Path Cᴰ.Hom[ ((G.F ⟅ x ⟆) N.⊗ (G.F ⟅ M.unit ⟆) , xᴰ P.⊗ᴰ unitᴰ') , (G.F ⟅ x ⟆ , xᴰ) ]
          (_ , liftIn (μ≅ x M.unit) (xᴰ P.⊗ᴰ unitᴰ') Cᴰ.⋆ᴰ ρᴰ'⟨ xᴰ ⟩)
          (_ , (Cᴰ.idᴰ P.⊗ₕᴰ liftOut ε≅ P.unitᴰ) Cᴰ.⋆ᴰ P.ρᴰ⟨ xᴰ ⟩)
    v⋆ρ' xᴰ =
        Cᴰ.⟨ refl ⟩⋆⟨ sym (R.reind-filler _ _) ⟩
      ∙ sym (Cᴰ.⋆Assoc _ _ _)
      ∙ Cᴰ.⟨ Cᴰ.≡in (liftIn⋆Out (μ≅ _ M.unit) (xᴰ P.⊗ᴰ unitᴰ')) ⟩⋆⟨ refl ⟩
      ∙ Cᴰ.⋆IdL _

    -- The right-hand leg of the triangle, with the μ-lifts cancelled.
    Z⋆S : ∀ {x y} (xᴰ : Rᴰ.ob[ x ]) (yᴰ : Rᴰ.ob[ y ])
      → Path Cᴰ.Hom[ (((G.F ⟅ x ⟆) N.⊗ (G.F ⟅ M.unit ⟆)) N.⊗ (G.F ⟅ y ⟆)
                     , (xᴰ P.⊗ᴰ unitᴰ') P.⊗ᴰ yᴰ)
                   , ((G.F ⟅ x ⟆) N.⊗ (G.F ⟅ y ⟆) , xᴰ P.⊗ᴰ yᴰ) ]
          (_ , (liftIn (μ≅ x M.unit) (xᴰ P.⊗ᴰ unitᴰ') P.⊗ₕᴰ Cᴰ.idᴰ {p = yᴰ})
               Cᴰ.⋆ᴰ (ρᴰ'⟨ xᴰ ⟩ P.⊗ₕᴰ Rᴰ.idᴰ {p = yᴰ}))
          (_ , ((Cᴰ.idᴰ P.⊗ₕᴰ liftOut ε≅ P.unitᴰ) P.⊗ₕᴰ Cᴰ.idᴰ {p = yᴰ})
               Cᴰ.⋆ᴰ (P.ρᴰ⟨ xᴰ ⟩ P.⊗ₕᴰ Cᴰ.idᴰ {p = yᴰ}))
    Z⋆S xᴰ yᴰ =
        sym (Cᴰ.≡in (P.─⊗ᴰ─ .F-seqᴰ _ _))
      ∙ ⟨ v⋆ρ' xᴰ ⟩⊗ₕᴰ⟨ id⋆Rid ⟩
      ∙ ⟨ refl ⟩⊗ₕᴰ⟨ sym (Cᴰ.⋆IdL _) ⟩
      ∙ Cᴰ.≡in (P.─⊗ᴰ─ .F-seqᴰ _ _)

    -- The left-hand leg of the triangle, reassembled into `id ⊗' η'`.
    W⋆η : ∀ {x y} (xᴰ : Rᴰ.ob[ x ]) (yᴰ : Rᴰ.ob[ y ])
      → Path Cᴰ.Hom[ ((G.F ⟅ x ⟆) N.⊗ (G.F ⟅ M.unit M.⊗ y ⟆)
                     , xᴰ P.⊗ᴰ (unitᴰ' ⊗ᴰ' yᴰ))
                   , ((G.F ⟅ x ⟆) N.⊗ (G.F ⟅ y ⟆) , xᴰ P.⊗ᴰ yᴰ) ]
          (_ , (Cᴰ.idᴰ {p = xᴰ} P.⊗ₕᴰ liftOut (μ≅ M.unit y) (unitᴰ' P.⊗ᴰ yᴰ))
               Cᴰ.⋆ᴰ ((Cᴰ.idᴰ {p = xᴰ} P.⊗ₕᴰ (liftOut ε≅ P.unitᴰ P.⊗ₕᴰ Cᴰ.idᴰ))
                      Cᴰ.⋆ᴰ (Cᴰ.idᴰ {p = xᴰ} P.⊗ₕᴰ P.ηᴰ⟨ yᴰ ⟩)))
          (_ , Rᴰ.idᴰ {p = xᴰ} P.⊗ₕᴰ ηᴰ'⟨ yᴰ ⟩)
    W⋆η xᴰ yᴰ =
        Cᴰ.⟨ refl ⟩⋆⟨ sym (Cᴰ.≡in (P.─⊗ᴰ─ .F-seqᴰ _ _)) ⟩
      ∙ sym (Cᴰ.≡in (P.─⊗ᴰ─ .F-seqᴰ _ _))
      ∙ ⟨ Cᴰ.⋆IdL _ ∙ Cᴰ.⋆IdL _ ∙ sym Rᴰid≡ ⟩⊗ₕᴰ⟨ R.reind-filler _ _ ⟩

  triangleᴰ' : ∀ {x y} (xᴰ : Rᴰ.ob[ x ]) (yᴰ : Rᴰ.ob[ y ])
    → (αᴰ'⟨ xᴰ , unitᴰ' , yᴰ ⟩ Rᴰ.⋆ᴰ (─⊗ᴰ'─ .F-homᴰ (ρᴰ'⟨ xᴰ ⟩ , Rᴰ.idᴰ)))
        Rᴰ.≡[ M.triangle x y ]
      (─⊗ᴰ'─ .F-homᴰ (Rᴰ.idᴰ , ηᴰ'⟨ yᴰ ⟩))
  triangleᴰ' xᴰ yᴰ = Cᴰ.rectify $ Cᴰ.≡out $
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
          ∙ Cᴰ.⟨ Z⋆S xᴰ yᴰ ⟩⋆⟨ refl ⟩
          ∙ Cᴰ.⋆Assoc _ _ _ ⟩
        ∙ sym (Cᴰ.⋆Assoc _ _ _)
        ∙ Cᴰ.⟨ sym (Cᴰ.≡in (P.αᴰ .transᴰ .N-homᴰ
                 (Cᴰ.idᴰ , (liftOut ε≅ P.unitᴰ , Cᴰ.idᴰ)))) ⟩⋆⟨ refl ⟩
        ∙ Cᴰ.⋆Assoc _ _ _
        ∙ Cᴰ.⟨ refl ⟩⋆⟨ sym (Cᴰ.⋆Assoc _ _ _)
                      ∙ Cᴰ.⟨ Cᴰ.≡in (P.triangleᴰ _ _) ⟩⋆⟨ refl ⟩ ⟩ ⟩
      ∙ Cᴰ.⟨ refl ⟩⋆⟨ sym (Cᴰ.⋆Assoc _ _ _) ⟩
      ∙ sym (Cᴰ.⋆Assoc _ _ _)
      ∙ Cᴰ.⟨ W⋆η xᴰ yᴰ ⟩⋆⟨ refl ⟩ ⟩
    ∙ R.reind-filler _ _

  private
    η'-sec : ∀ {x} (xᴰ : Rᴰ.ob[ x ])
      → (η⁻¹ᴰ'⟨ xᴰ ⟩ Rᴰ.⋆ᴰ ηᴰ'⟨ xᴰ ⟩) Rᴰ.≡[ M.η .nIso x .sec ] Rᴰ.idᴰ
    η'-sec xᴰ = Cᴰ.rectify $ Cᴰ.≡out $
        sym (R.reind-filler _ _)
      ∙ Cᴰ.⟨ sym (R.reind-filler _ _) ⟩⋆⟨ sym (R.reind-filler _ _) ⟩
      ∙ Cᴰ.⋆Assoc _ _ _
      ∙ Cᴰ.⟨ refl ⟩⋆⟨ sym (Cᴰ.⋆Assoc _ _ _)
                    ∙ Cᴰ.⟨ Cᴰ.≡in (liftIn⋆Out (μ≅ _ _) _) ⟩⋆⟨ refl ⟩
                    ∙ Cᴰ.⋆IdL _ ⟩
      ∙ Cᴰ.⋆Assoc _ _ _
      ∙ Cᴰ.⟨ refl ⟩⋆⟨ sym (Cᴰ.⋆Assoc _ _ _)
                    ∙ Cᴰ.⟨ sym (Cᴰ.≡in (P.─⊗ᴰ─ .F-seqᴰ _ _))
                         ∙ ⟨ Cᴰ.≡in (liftIn⋆Out ε≅ _) ⟩⊗ₕᴰ⟨ Cᴰ.⋆IdL _ ⟩
                         ∙ Cᴰ.≡in (P.─⊗ᴰ─ .F-idᴰ) ⟩⋆⟨ refl ⟩
                    ∙ Cᴰ.⋆IdL _ ⟩
      ∙ Cᴰ.≡in (P.ηᴰ .nIsoᴰ _ .secᴰ)
      ∙ sym Rᴰid≡

    η'-ret : ∀ {x} (xᴰ : Rᴰ.ob[ x ])
      → (ηᴰ'⟨ xᴰ ⟩ Rᴰ.⋆ᴰ η⁻¹ᴰ'⟨ xᴰ ⟩) Rᴰ.≡[ M.η .nIso x .ret ] Rᴰ.idᴰ
    η'-ret xᴰ = Cᴰ.rectify $ Cᴰ.≡out $
        sym (R.reind-filler _ _)
      ∙ Cᴰ.⟨ sym (R.reind-filler _ _) ⟩⋆⟨ sym (R.reind-filler _ _) ⟩
      ∙ Cᴰ.⋆Assoc _ _ _
      ∙ Cᴰ.⟨ refl ⟩⋆⟨
            Cᴰ.⋆Assoc _ _ _
          ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⋆Assoc _ _ _ ⟩
                        ∙ sym (Cᴰ.⋆Assoc _ _ _)
                        ∙ Cᴰ.⟨ Cᴰ.≡in (P.ηᴰ .nIsoᴰ _ .retᴰ) ⟩⋆⟨ refl ⟩
                        ∙ Cᴰ.⋆IdL _ ⟩
          ∙ sym (Cᴰ.⋆Assoc _ _ _)
          ∙ Cᴰ.⟨ sym (Cᴰ.≡in (P.─⊗ᴰ─ .F-seqᴰ _ _))
               ∙ ⟨ Cᴰ.≡in (liftOut⋆In ε≅ _) ⟩⊗ₕᴰ⟨ Cᴰ.⋆IdL _ ⟩
               ∙ Cᴰ.≡in (P.─⊗ᴰ─ .F-idᴰ) ⟩⋆⟨ refl ⟩
          ∙ Cᴰ.⋆IdL _ ⟩
      ∙ Cᴰ.≡in (liftOut⋆In (μ≅ _ _) _)
      ∙ sym Rᴰid≡
