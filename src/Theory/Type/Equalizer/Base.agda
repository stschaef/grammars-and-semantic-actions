open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Equalizer.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Inductive.Base σeq V vs 𝒫

private variable ℓA ℓB ℓC ℓX : Level

module _ {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} (f f' : A ⊢ B) where
  equalizer : TheoryTy (ℓ-max ℓA ℓB) s
  equalizer m = Σ[ x ∈ A m ] f m x ≡ f' m x

  eq-π : equalizer ⊢ A
  eq-π = λ m z → z .fst

  eq-π-pf : f ∘⊢ eq-π ≡ f' ∘⊢ eq-π
  eq-π-pf i m x = x .snd i

  module _ {C : TheoryTy ℓC s} (f'' : C ⊢ A) (p : f ∘⊢ f'' ≡ f' ∘⊢ f'') where
    eq-intro : C ⊢ equalizer
    eq-intro m x .fst = f'' m x
    eq-intro m x .snd i = p i m x

    eq-β : eq-π ∘⊢ eq-intro ≡ f''
    eq-β = refl

  equalizer-section : (f'' : A ⊢ equalizer) → eq-π ∘⊢ f'' ≡ id⊢ → f ≡ f'
  equalizer-section f'' p =
    cong (f ∘⊢_) (sym p)
    ∙ cong (_∘⊢ f'') eq-π-pf
    ∙ cong (f' ∘⊢_) p

module _ {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {C : TheoryTy ℓC s}
  (f f' : A ⊢ B) (f'' : B ⊢ C) where
  equalizer-cong : equalizer f f' ⊢ equalizer (f'' ∘⊢ f) (f'' ∘⊢ f')
  equalizer-cong =
    eq-intro (f'' ∘⊢ f) (f'' ∘⊢ f') (eq-π f f') (cong (f'' ∘⊢_) (eq-π-pf f f'))

module _ {ℓA ℓX} {X : Type ℓX} {xs : X → S}
  (F : (x : X) → Functor ℓA X xs (xs x))
  (A : (x : X) → TheoryTy ℓB (xs x))
  (e e' : ∀ (x : X) → μ F x ⊢ A x)
  (pf : ∀ (x : X) →
    e  x ∘⊢ roll ∘⊢ map (F x) (λ x' → eq-π (e x') (e' x')) ≡
    e' x ∘⊢ roll ∘⊢ map (F x) (λ x' → eq-π (e x') (e' x')))
  where

  equalizer-ind-alg : ∀ x
    → ⟦ F x ⟧TheoryTy (λ x → equalizer (e x) (e' x)) ⊢ equalizer (e x) (e' x)
  equalizer-ind-alg x =
    eq-intro (e x) (e' x)
      (roll ∘⊢ map (F x) (λ x' → eq-π (e x') (e' x')))
      (pf x)

  equalizer-ind : ∀ (x : X) → e x ≡ e' x
  equalizer-ind x =
    equalizer-section (e x) (e' x)
      (rec F equalizer-ind-alg x)
      (rec-section F equalizer-ind-alg
        (λ x' → eq-π (e x') (e' x'))
        (λ x' → refl) x)

equalizer-ind-unit : ∀ {s : S} (F : Functor ℓA Unit (λ _ → s) s)
  (A : TheoryTy ℓB s)
  (e e' : μ {X = Unit} {xs = λ _ → s} (λ _ → F) tt ⊢ A)
  → (e ∘⊢ roll ∘⊢ map F (λ _ → eq-π e e'))
    ≡ (e' ∘⊢ roll ∘⊢ map F (λ _ → eq-π e e'))
  → e ≡ e'
equalizer-ind-unit F A e e' pf =
  equalizer-ind (λ _ → F) (λ _ → A) _ _ (λ _ → pf) tt
