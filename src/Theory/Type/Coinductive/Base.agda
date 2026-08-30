{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Coinductive.Base
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
  record ν (F : (x : X) → Functor ℓA X xs (xs x)) (x : X) (m : ↓M (xs x))
    : Type (ℓF ℓA ⊔ℓ ℓX) where
    coinductive
    field
      unroll : ⟦ F x ⟧TheoryTy (ν F) m

  open ν public

  module _ (F : (x : X) → Functor ℓA X xs (xs x)) where
    finalCoalgebra : ∀ x → ν F x ⊢ ⟦ F x ⟧TheoryTy (ν F)
    finalCoalgebra x m t = t .unroll

    module _ {ℓB : Level} {A : (x : X) → TheoryTy ℓB (xs x)}
      (α : ∀ x → A x ⊢ ⟦ F x ⟧TheoryTy A) where

      CoRecHomo : Type _
      CoRecHomo =
        Σ[ ϕ ∈ (∀ x → A x ⊢ ν F x) ]
          (∀ x → map (F x) ϕ ∘⊢ α x ≡ finalCoalgebra x ∘⊢ ϕ x)

      -- Productive rather than structural: every corecursive call sits
      -- under an `unroll` field, but reaches it through `map (F x)`, which
      -- the checker cannot see into.  See the note on `fold` in
      -- `Type/Guarded/Base`.
      {-# TERMINATING #-}
      corecHomo : CoRecHomo
      corecHomo .fst x m a .unroll = map (F x) (corecHomo .fst) m (α x m a)
      corecHomo .snd x = refl

      corec : ∀ x → A x ⊢ ν F x
      corec = corecHomo .fst

      module _ (ϕ : CoRecHomo) where
        private
          -- A proof, not a definition, with the same hidden productivity
          -- as `corecHomo`: each call is under an `unroll`, behind
          -- `map (F x)`.  See the note on `fold` in `Type/Guarded/Base`.
          {-# TERMINATING #-}
          ν-η' : ∀ x m a → ϕ .fst x m a ≡ corec x m a
          ν-η' x m a i .unroll =
            ((λ j → ϕ .snd x (~ j) m a)
            ∙ (λ j → map (F x) (λ y m' a' → ν-η' y m' a' j) m (α x m a))) i
        ν-η : ϕ .fst ≡ corec
        ν-η = funExt λ x → funExt λ m → funExt λ a → ν-η' x m a

      coind : (ϕ ϕ' : CoRecHomo) → ϕ .fst ≡ ϕ' .fst
      coind ϕ ϕ' = ν-η ϕ ∙ sym (ν-η ϕ')

      coind' : (ϕ ϕ' : CoRecHomo) → ∀ x → ϕ .fst x ≡ ϕ' .fst x
      coind' ϕ ϕ' = funExt⁻ (coind ϕ ϕ')

    coind-id : (ϕ : CoRecHomo finalCoalgebra) → ϕ .fst ≡ λ x → id⊢
    coind-id ϕ = coind finalCoalgebra ϕ
      ((λ x → id⊢) , λ x → cong (_∘⊢ finalCoalgebra x) (map-id (F x)))

    coind-id' : (ϕ : CoRecHomo finalCoalgebra) → ∀ x → ϕ .fst x ≡ id⊢
    coind-id' ϕ x = funExt⁻ (coind-id ϕ) x

    module _ {ℓB : Level} {A : (x : X) → TheoryTy ℓB (xs x)}
      (α : ∀ x → A x ⊢ ⟦ F x ⟧TheoryTy A)
      (gmap : ∀ x → ν F x ⊢ A x)
      (gpf : ∀ x → α x ∘⊢ gmap x ≡ map (F x) gmap ∘⊢ finalCoalgebra x) where
      private
        corec-retract-homo : CoRecHomo finalCoalgebra
        corec-retract-homo .fst x = corec α x ∘⊢ gmap x
        corec-retract-homo .snd x =
          cong (_∘⊢ finalCoalgebra x) (map-∘ (F x) (corec α) gmap)
          ∙ cong (map (F x) (corec α) ∘⊢_) (sym (gpf x))
          ∙ cong (_∘⊢ gmap x) (corecHomo α .snd x)
      corec-retract : ∀ x → corec α x ∘⊢ gmap x ≡ id⊢
      corec-retract = coind-id' corec-retract-homo

    roll-ν : ∀ x → ⟦ F x ⟧TheoryTy (ν F) ⊢ ν F x
    roll-ν = corec {A = λ x → ⟦ F x ⟧TheoryTy (ν F)} coalg where
      coalg : ∀ x → ⟦ F x ⟧TheoryTy (ν F)
                  ⊢ ⟦ F x ⟧TheoryTy (λ x → ⟦ F x ⟧TheoryTy (ν F))
      coalg x = map (F x) finalCoalgebra
