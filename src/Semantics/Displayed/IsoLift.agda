{-# OPTIONS --lossy-unification #-}
{- Displayed isomorphisms from cartesian lifts.

   ccl's `WeakIsoLift` gives a section and a retraction of a base
   isomorphism but *no equations* between them: with `hasPropHoms` the
   equations are free. For the proof-relevant setting they are not, so
   we build the strong version, where the lift is a genuine `isIsoᴰ`,
   out of a cartesian lift along the iso.
-}
module Semantics.Displayed.IsoLift where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  open isIso
  open isIsoᴰ

  module _ {x y} {φ : C [ x , y ]} (φIso : isIso C φ) {yᴰ : Cᴰ.ob[ y ]}
    (φ*yᴰ : CartesianLift Cᴰ φ yᴰ) where
    private
      module L = CartesianLiftNotation Cᴰ φ*yᴰ

    -- | The projection out of the lift, rectified to sit over `φ`.
    liftπ : Cᴰ.Hom[ φ ][ φ*yᴰ .fst , yᴰ ]
    liftπ = Cᴰ.reind (C.⋆IdL φ) L.πⱽ

    -- | Its inverse, obtained from the universal property applied to
    --   the identity.
    liftσ : Cᴰ.Hom[ φIso .inv ][ yᴰ , φ*yᴰ .fst ]
    liftσ = L.introᴰ (Cᴰ.reind (sym (φIso .sec)) Cᴰ.idᴰ)

    isIsoᴰliftπ : isIsoᴰ Cᴰ φIso liftπ
    isIsoᴰliftπ .invᴰ = liftσ
    isIsoᴰliftπ .secᴰ = Cᴰ.rectify $ Cᴰ.≡out $
      Cᴰ.⟨ refl ⟩⋆⟨ sym (Cᴰ.reind-filler _) ⟩
      ∙ L.βᴰ' _
      ∙ sym (Cᴰ.reind-filler _)
    isIsoᴰliftπ .retᴰ = L.extensionalityᴰin (φIso .ret) $
      L.⋆πⱽ-natural
      ∙ Cᴰ.⟨ refl ⟩⋆⟨ L.βᴰ _ ∙ sym (Cᴰ.reind-filler _) ⟩
      ∙ Cᴰ.⋆IdR _
      ∙ sym (Cᴰ.reind-filler _)

  -- | Packaged: in a fibration, every base isomorphism transports
  --   displayed objects backwards, coherently.
  module IsoLifts (cartLifts : isFibration Cᴰ) where
    liftOb : ∀ {x y} (φ : CatIso C x y) (yᴰ : Cᴰ.ob[ y ]) → Cᴰ.ob[ x ]
    liftOb φ yᴰ = cartLifts yᴰ _ (φ .fst) .fst

    liftIso : ∀ {x y} (φ : CatIso C x y) (yᴰ : Cᴰ.ob[ y ])
      → CatIsoᴰ Cᴰ φ (liftOb φ yᴰ) yᴰ
    liftIso φ yᴰ = liftπ (φ .snd) (cartLifts yᴰ _ (φ .fst))
                 , isIsoᴰliftπ (φ .snd) (cartLifts yᴰ _ (φ .fst))

    -- | `π`: from the transported object down to the original.
    liftOut : ∀ {x y} (φ : CatIso C x y) (yᴰ : Cᴰ.ob[ y ])
      → Cᴰ.Hom[ φ .fst ][ liftOb φ yᴰ , yᴰ ]
    liftOut φ yᴰ = liftIso φ yᴰ .fst

    -- | `σ`: its inverse.
    liftIn : ∀ {x y} (φ : CatIso C x y) (yᴰ : Cᴰ.ob[ y ])
      → Cᴰ.Hom[ φ .snd .inv ][ yᴰ , liftOb φ yᴰ ]
    liftIn φ yᴰ = liftIso φ yᴰ .snd .invᴰ

    liftIn⋆Out : ∀ {x y} (φ : CatIso C x y) (yᴰ : Cᴰ.ob[ y ])
      → (liftIn φ yᴰ Cᴰ.⋆ᴰ liftOut φ yᴰ) Cᴰ.≡[ φ .snd .sec ] Cᴰ.idᴰ
    liftIn⋆Out φ yᴰ = liftIso φ yᴰ .snd .secᴰ

    liftOut⋆In : ∀ {x y} (φ : CatIso C x y) (yᴰ : Cᴰ.ob[ y ])
      → (liftOut φ yᴰ Cᴰ.⋆ᴰ liftIn φ yᴰ) Cᴰ.≡[ φ .snd .ret ] Cᴰ.idᴰ
    liftOut⋆In φ yᴰ = liftIso φ yᴰ .snd .retᴰ
