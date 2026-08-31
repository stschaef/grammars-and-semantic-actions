open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Top.Properties
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Equality as Eq
open import Cubical.WildCat.LocallySmall.Base

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Top.Base σeq V vs 𝒫
open import Theory.Type.Sum.Base σeq V vs 𝒫
open import Theory.Type.Inductive.Base σeq V vs 𝒫
open import Theory.Type.Coinductive.Base σeq V vs 𝒫 using (ν ; corec ; corec-retract)
open import Theory.Type.Equalizer.Base σeq V vs 𝒫
open import Theory.Type.Guarded.Base σeq V vs 𝒫

open WildCatNotation
open WildCatIso

private variable ℓA ℓR : Level

module _ {s : S} {A : TheoryTy ℓA s} where
  ≅⊤Ty : (i : ⊤Ty ⊢ A) → i ∘⊢ ⊤Ty-intro ≡ id⊢ → ⊤Ty ≅ A
  ≅⊤Ty i r .fun = i
  ≅⊤Ty i r .inv = ⊤Ty-intro
  ≅⊤Ty i r .sec = r
  ≅⊤Ty i r .ret = ⊤Ty-η _ ∙ sym (⊤Ty-η id⊢)

module _ {s : S} where
  ⊤→⊕⌈⌉ : ⊤Ty ⊢ ⊕[ m ∈ ↓M s ] ⌈ m ⌉
  ⊤→⊕⌈⌉ m _ = m , Eq.refl

  ⊤≅⊕⌈⌉ : ⊤Ty ≅ (⊕ᴰ (↓M s) λ m → ⌈ m ⌉)
  ⊤≅⊕⌈⌉ = ≅⊤Ty ⊤→⊕⌈⌉ (funExt λ m → funExt λ where (m' , Eq.refl) → refl)

module _ (F : (s : S) → Functor ℓA S (λ s → s) s)
  {R : Pt (λ s → s) → Pt (λ s → s) → Type ℓR}
  (L : Löb R (μ F)) where

  open Löb L

  Step : Type _
  Step = ∀ s → ▷ s ⊢ μ F s

  module _ (step : Step) where
    intro : ∀ s → ⊤Ty ⊢ μ F s
    intro = löb step

    intro-unfold : ∀ s → intro s ≡ step s ∘⊢ next intro s
    intro-unfold = löb-unfold step

    private
      retr : ∀ s → μ F s ⊢ μ F s
      retr s = intro s ∘⊢ ⊤Ty-intro

      π* : ∀ s → equalizer (retr s) id⊢ ⊢ μ F s
      π* s = eq-π (retr s) id⊢

    Unambiguous : Type _
    Unambiguous = ∀ s → retr s ∘⊢ roll ∘⊢ map (F s) π*
                  ≡ id⊢ ∘⊢ roll ∘⊢ map (F s) π*

    module _ (unamb : Unambiguous) where
      retr≡id : ∀ s → retr s ≡ id⊢
      retr≡id = equalizer-ind F (λ s → μ F s) retr (λ _ → id⊢) unamb

      ⊤≅μ : ∀ s → ⊤Ty ≅ μ F s
      ⊤≅μ s = ≅⊤Ty (intro s) (retr≡id s)

      private
        isContrμ : ∀ s m → isContr (μ F s m)
        isContrμ s m .fst = intro s m tt
        isContrμ s m .snd t i = retr≡id s i m t

        isoFμ : ∀ s m → Iso (⟦ F s ⟧TheoryTy (μ F) m) (μ F s m)
        isoFμ s m .Iso.fun = roll m
        isoFμ s m .Iso.inv = unroll F s m
        isoFμ s m .Iso.sec t = funExt⁻ (funExt⁻ (roll-unroll F s) m) t
        isoFμ s m .Iso.ret z = refl

        isoF⊤ : ∀ s m
          → Iso (⟦ F s ⟧TheoryTy (λ _ → ⊤Ty) m) (⟦ F s ⟧TheoryTy (μ F) m)
        isoF⊤ s m .Iso.fun = map (F s) intro m
        isoF⊤ s m .Iso.inv = map (F s) (λ _ → ⊤Ty-intro) m
        isoF⊤ s m .Iso.sec z =
          funExt⁻ (funExt⁻
            (map-inv (F s) intro (λ _ → ⊤Ty-intro) retr≡id) m) z
        isoF⊤ s m .Iso.ret t =
          funExt⁻ (funExt⁻
            (map-inv (F s) (λ _ → ⊤Ty-intro) intro
              (λ _ → ⊤Ty-η _ ∙ sym (⊤Ty-η id⊢))) m) t

        isContrF⊤ : ∀ s m → isContr (⟦ F s ⟧TheoryTy (λ _ → ⊤Ty) m)
        isContrF⊤ s m =
          isOfHLevelRetractFromIso 0 (isoF⊤ s m)
            (isOfHLevelRetractFromIso 0 (isoFμ s m) (isContrμ s m))

        γ : ∀ s → ⊤Ty ⊢ ⟦ F s ⟧TheoryTy (λ _ → ⊤Ty)
        γ s m _ = isContrF⊤ s m .fst

      ⊤≅ν : ∀ s → ⊤Ty ≅ ν F s
      ⊤≅ν s =
        ≅⊤Ty (corec F γ s)
          (corec-retract F γ (λ _ → ⊤Ty-intro)
            (λ s' → funExt λ m → funExt λ t →
               isContr→isProp (isContrF⊤ s' m) _ _)
            s)
