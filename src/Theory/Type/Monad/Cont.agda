open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Monad.Cont
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Function.Base σeq V vs 𝒫
open import Theory.Type.Monad.Base σeq V vs 𝒫

module _ {ℓR} (R : ∀ {s} → TheoryTy ℓR s) where
  Cont : ∀ {ℓA} {s} → TheoryTy ℓA s → TheoryTy (ℓ-max ℓA ℓR) s
  Cont A = (A ⇒ R) ⇒ R

  ContMonad : Monad
  ContMonad .ℓT ℓA = ℓ-max ℓA ℓR
  ContMonad .T = Cont
  ContMonad .η m a k = k a
  ContMonad .bind f m c k = c (λ a → f m a k)
  ContMonad .bind-η = refl
  ContMonad .bind-β f = refl
  ContMonad .bind-assoc g f = refl

  callCC : ∀ {ℓA ℓB} {s} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
    → ((A ⇒ Cont B) ⇒ Cont A) ⊢ Cont A
  callCC m f k = f (λ a _ → k a) k

  abort : ∀ {ℓA} {s} {A : TheoryTy ℓA s} → R ⊢ Cont A
  abort m r k = r
