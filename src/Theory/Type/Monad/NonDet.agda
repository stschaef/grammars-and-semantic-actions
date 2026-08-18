{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Monad.NonDet
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Foundations.More
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Top.Base σeq V vs 𝒫
open import Theory.Type.Lift.Base σeq V vs 𝒫
open import Theory.Type.Inductive.Base σeq V vs 𝒫
open import Theory.Type.Monad.Base σeq V vs 𝒫
open import Theory.Type.Sum.Base σeq V vs 𝒫
open import Theory.Type.Product.Base σeq V vs 𝒫
open import Theory.Type.Product.Binary.Base σeq V vs 𝒫
open import Theory.Type.Function.Base σeq V vs 𝒫
open import Theory.Type.Equalizer.Base σeq V vs 𝒫

private variable ℓA ℓB ℓC : Level

module _ {s : S} where
  listBranch : TheoryTy ℓA s → Bool → Functor ℓA Unit (λ _ → s) s
  listBranch {ℓA = ℓA} A false = k (LiftTheoryTy ℓA ⊤Ty)
  listBranch A true = k A &e2 Var tt

  ListCode : TheoryTy ℓA s → Functor ℓA Unit (λ _ → s) s
  ListCode A = ⊕e Bool (listBranch A)

  ND : TheoryTy ℓA s → TheoryTy (ℓF ℓA) s
  ND A = μ {X = Unit} {xs = λ _ → s} (λ _ → ListCode A) tt

module _ {s : S} {A : TheoryTy ℓA s} where
  nilND : ⊤Ty ⊢ ND A
  nilND = roll ∘⊢ σ⊕ false ∘⊢ liftTy ∘⊢ liftTy

  cons : ∀ {ℓC} {C : TheoryTy ℓC s} → C ⊢ A → C ⊢ ND A → C ⊢ ND A
  cons h t = roll ∘⊢ σ⊕ true ∘⊢ ((liftTy ∘⊢ h) ,& (liftTy ∘⊢ t))

  consND : A & ND A ⊢ ND A
  consND = cons π₁ π₂

  ηND : A ⊢ ND A
  ηND = cons id⊢ (nilND ∘⊢ ⊤Ty-intro)

  appendND : ND A & ND A ⊢ ND A
  appendND = ⇒-intro⁻ (rec (λ _ → ListCode A) (λ _ → alg) _)
    where
    alg : ⟦ ListCode A ⟧TheoryTy (λ _ → ND A ⇒ ND A) ⊢ ND A ⇒ ND A
    alg = ⊕ᴰ-elim λ where
      false → ⇒-intro π₂
      true → ⇒-intro (cons (lowerTy ∘⊢ π₁ ∘⊢ π₁)
        (⇒-app ∘⊢ ((lowerTy ∘⊢ π₂ ∘⊢ π₁) ,& π₂)))

module _ {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} (f : A ⊢ ND B) where
  bindND : ND A ⊢ ND B
  bindND = rec (λ _ → ListCode A) (λ _ → alg) _
    where
    alg : ⟦ ListCode A ⟧TheoryTy (λ _ → ND B) ⊢ ND B
    alg = ⊕ᴰ-elim λ where
      false → nilND ∘⊢ ⊤Ty-intro
      true → appendND ∘⊢ ((f ∘⊢ lowerTy ∘⊢ π₁) ,& (lowerTy ∘⊢ π₂))

module _ {s : S} {A : TheoryTy ℓA s} where
  append-nil : appendND ∘⊢ (id⊢ ,& (nilND ∘⊢ ⊤Ty-intro)) ≡ id⊢ {A = ND A}
  append-nil =
    equalizer-ind (λ _ → ListCode A) (λ _ → ND A)
      (λ _ → appendND ∘⊢ (id⊢ ,& (nilND ∘⊢ ⊤Ty-intro)))
      (λ _ → id⊢)
      (λ _ → ⊕ᴰ≡ _ _ λ where
        false → refl
        true i → cons (lowerTy ∘⊢ π₁)
                      (eq-π-pf _ _ i ∘⊢ lowerTy ∘⊢ π₂))
      tt

  appL appR : ND A ⊢ ND A ⇒ (ND A ⇒ ND A)
  appL = ⇒-intro (⇒-intro (appendND ∘⊢ ((appendND ∘⊢ π₁) ,& π₂)))
  appR = ⇒-intro (⇒-intro
    (appendND ∘⊢ ((π₁ ∘⊢ π₁) ,& (appendND ∘⊢ ((π₂ ∘⊢ π₁) ,& π₂)))))

  append-assoc : appL ≡ appR
  append-assoc =
    equalizer-ind (λ _ → ListCode A) (λ _ → ND A ⇒ (ND A ⇒ ND A))
      (λ _ → appL)
      (λ _ → appR)
      (λ _ → ⊕ᴰ≡ _ _ λ where
        false → refl
        true i → ⇒-intro (⇒-intro (cons (lowerTy ∘⊢ π₁ ∘⊢ π₁ ∘⊢ π₁)
          (⇒-app ∘⊢ ((⇒-app ∘⊢ ((eq-π-pf _ _ i ∘⊢ lowerTy ∘⊢ π₂ ∘⊢ π₁ ∘⊢ π₁)
                                ,& (π₂ ∘⊢ π₁))) ,& π₂)))))
      tt

  bindND-η : bindND (ηND {A = A}) ≡ id⊢
  bindND-η =
    equalizer-ind (λ _ → ListCode A) (λ _ → ND A)
      (λ _ → bindND ηND)
      (λ _ → id⊢)
      (λ _ → ⊕ᴰ≡ _ _ λ where
        false → refl
        true i → cons (lowerTy ∘⊢ π₁)
                      (eq-π-pf _ _ i ∘⊢ lowerTy ∘⊢ π₂))
      tt

module _ {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} (f : A ⊢ ND B) where
  bindND-β : bindND f ∘⊢ ηND ≡ f
  bindND-β = cong (_∘⊢ f) (append-nil {A = B})

module _ {s : S} {B : TheoryTy ℓB s} {C : TheoryTy ℓC s} (g : B ⊢ ND C) where
  private
    bindAppL bindAppR : ND B ⊢ ND B ⇒ ND C
    bindAppL = ⇒-intro (bindND g ∘⊢ appendND)
    bindAppR = ⇒-intro (appendND ∘⊢ ((bindND g ∘⊢ π₁) ,& (bindND g ∘⊢ π₂)))

    q : equalizer bindAppL bindAppR ⊢ ND B
    q = eq-π bindAppL bindAppR

  bind-append : bindAppL ≡ bindAppR
  bind-append =
    equalizer-ind (λ _ → ListCode B) (λ _ → ND B ⇒ ND C)
      (λ _ → bindAppL)
      (λ _ → bindAppR)
      (λ _ → ⊕ᴰ≡ _ _ λ where
        false → refl
        true →
          (λ i → ⇒-intro (appendND ∘⊢ ((g ∘⊢ lowerTy ∘⊢ π₁ ∘⊢ π₁)
            ,& (⇒-app ∘⊢ ((eq-π-pf _ _ i ∘⊢ lowerTy ∘⊢ π₂ ∘⊢ π₁) ,& π₂)))))
          ∙ (λ i → ⇒-intro (⇒-app ∘⊢ ((⇒-app ∘⊢
              ((append-assoc (~ i) ∘⊢ g ∘⊢ lowerTy ∘⊢ π₁ ∘⊢ π₁)
               ,& (bindND g ∘⊢ q ∘⊢ lowerTy ∘⊢ π₂ ∘⊢ π₁)))
              ,& (bindND g ∘⊢ π₂)))))
      tt

module _ {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {C : TheoryTy ℓC s}
  (g : B ⊢ ND C) (f : A ⊢ ND B) where
  private
    p₂ : equalizer (bindND g ∘⊢ bindND f) (bindND (bindND g ∘⊢ f)) ⊢ ND A
    p₂ = eq-π (bindND g ∘⊢ bindND f) (bindND (bindND g ∘⊢ f))

  bindND-assoc : bindND g ∘⊢ bindND f ≡ bindND (bindND g ∘⊢ f)
  bindND-assoc =
    equalizer-ind (λ _ → ListCode A) (λ _ → ND C)
      (λ _ → bindND g ∘⊢ bindND f)
      (λ _ → bindND (bindND g ∘⊢ f))
      (λ _ → ⊕ᴰ≡ _ _ λ where
        false → refl
        true →
          (λ i → ⇒-app ∘⊢ ((bind-append g i ∘⊢ f ∘⊢ lowerTy ∘⊢ π₁)
            ,& (bindND f ∘⊢ p₂ ∘⊢ lowerTy ∘⊢ π₂)))
          ∙ (λ i → appendND ∘⊢ ((bindND g ∘⊢ f ∘⊢ lowerTy ∘⊢ π₁)
            ,& (eq-π-pf _ _ i ∘⊢ lowerTy ∘⊢ π₂))))
      tt

NDMonad : Monad
NDMonad .ℓT = ℓF
NDMonad .T A = ND A
NDMonad .η = ηND
NDMonad .bind f = bindND f
NDMonad .bind-η = bindND-η
NDMonad .bind-β f = bindND-β f
NDMonad .bind-assoc g f = bindND-assoc g f
