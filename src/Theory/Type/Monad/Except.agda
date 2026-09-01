open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Monad.Except
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Sum.Binary.Base σeq V vs 𝒫
open import Theory.Type.Monad.Base σeq V vs 𝒫

module _ {ℓE} (E : ∀ {s} → TheoryTy ℓE s) where
  Except : ∀ {ℓA} {s} → TheoryTy ℓA s → TheoryTy (ℓ-max ℓA ℓE) s
  Except A = A ⊕ E

  module _ {ℓA} {s} {A : TheoryTy ℓA s} where
    ok : A ⊢ Except A
    ok = inl

    throw : E ⊢ Except A
    throw = inr

  ExceptMonad : Monad
  ExceptMonad .ℓT ℓA = ℓ-max ℓA ℓE
  ExceptMonad .T = Except
  ExceptMonad .η = inl
  ExceptMonad .bind f = ⊕-elim f inr
  ExceptMonad .bind-η = ⊕-η id⊢
  ExceptMonad .bind-β f = ⊕-βl f inr
  ExceptMonad .bind-assoc g f = ⊕≡ _ _ refl refl

  catch : ∀ {ℓA ℓB} {s} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
    → A ⊢ B → E ⊢ B → Except A ⊢ B
  catch = ⊕-elim
