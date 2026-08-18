{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Inductive.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Foundations.More
open import Cubical.Data.Sigma

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Code.Base σeq V vs 𝒫 public

module _ {ℓA ℓX} {X : Type ℓX} {xs : X → S} where

  data μ (F : (x : X) → Functor ℓA X xs (xs x)) (x : X)
    : TheoryTy (ℓF ℓA ⊔ℓ ℓX) (xs x) where
    roll : ⟦ F x ⟧TheoryTy (μ F) ⊢ μ F x

  module _ (F : (x : X) → Functor ℓA X xs (xs x)) where
    initialAlgebra : ∀ x → ⟦ F x ⟧TheoryTy (μ F) ⊢ μ F x
    initialAlgebra x = roll

    module _ {ℓB : Level} {A : (x : X) → TheoryTy ℓB (xs x)}
      (α : ∀ x → ⟦ F x ⟧TheoryTy A ⊢ A x) where

      RecHomo : Type _
      RecHomo =
        Σ[ ϕ ∈ (∀ x → μ F x ⊢ A x) ]
          (∀ x → ϕ x ∘⊢ roll ≡ α x ∘⊢ map (F x) ϕ)

      {-# TERMINATING #-}
      rec : ∀ x → μ F x ⊢ A x
      rec x m (roll ._ z) = α x m (map (F x) rec m z)

      recHomo : RecHomo
      recHomo .fst = rec
      recHomo .snd x = refl

      module _ (ϕ : RecHomo) where
        private
          {-# TERMINATING #-}
          μ-η' : ∀ x m z → ϕ .fst x m z ≡ rec x m z
          μ-η' x m (roll _ z) =
            (λ i → ϕ .snd x i m z)
            ∙ λ i → α x m (map (F x) (λ x m z → μ-η' x m z i) m z)
        μ-η : ϕ .fst ≡ rec
        μ-η = funExt λ x → funExt λ m → funExt λ z → μ-η' x m z

      ind : (ϕ ϕ' : RecHomo) → ϕ .fst ≡ ϕ' .fst
      ind ϕ ϕ' = μ-η ϕ ∙ sym (μ-η ϕ')

      ind' : (ϕ ϕ' : RecHomo) → ∀ x → ϕ .fst x ≡ ϕ' .fst x
      ind' ϕ ϕ' = funExt⁻ (ind ϕ ϕ')

    ind-id : (ϕ : RecHomo initialAlgebra) → ϕ .fst ≡ λ x → id⊢
    ind-id ϕ = ind initialAlgebra ϕ
      ((λ x → id⊢) , λ x → cong (roll ∘⊢_) (sym (map-id (F x))))

    ind-id' : (ϕ : RecHomo initialAlgebra) → ∀ x → ϕ .fst x ≡ id⊢
    ind-id' ϕ x = funExt⁻ (ind-id ϕ) x

    module _ {ℓB : Level} {A : (x : X) → TheoryTy ℓB (xs x)}
      (α : ∀ x → ⟦ F x ⟧TheoryTy A ⊢ A x)
      (gmap : ∀ x → A x ⊢ μ F x)
      (gpf : ∀ x → gmap x ∘⊢ α x ≡ roll ∘⊢ map (F x) gmap) where
      private
        rec-section-homo : RecHomo initialAlgebra
        rec-section-homo .fst x = gmap x ∘⊢ rec α x
        rec-section-homo .snd x =
          cong (gmap x ∘⊢_) (recHomo α .snd x)
          ∙ cong (_∘⊢ map (F x) (rec α)) (gpf x)
          ∙ cong (roll ∘⊢_) (sym (map-∘ (F x) gmap (rec α)))
      rec-section : ∀ x → gmap x ∘⊢ rec α x ≡ id⊢
      rec-section = ind-id' rec-section-homo

    unroll : ∀ x → μ F x ⊢ ⟦ F x ⟧TheoryTy (μ F)
    unroll x m (roll .m z) = z

    roll-unroll : ∀ x → roll ∘⊢ unroll x ≡ id⊢
    roll-unroll x = funExt λ m → funExt λ where (roll ._ z) → refl

    unroll-roll : ∀ x → unroll x ∘⊢ roll ≡ id⊢
    unroll-roll x = refl

    unroll' : ∀ x → μ F x ⊢ ⟦ F x ⟧TheoryTy (μ F)
    unroll' = rec {A = λ x → ⟦ F x ⟧TheoryTy (μ F)} alg where
      alg : ∀ x → ⟦ F x ⟧TheoryTy (λ x → ⟦ F x ⟧TheoryTy (μ F))
                ⊢ ⟦ F x ⟧TheoryTy (μ F)
      alg x = map (F x) λ _ → roll
