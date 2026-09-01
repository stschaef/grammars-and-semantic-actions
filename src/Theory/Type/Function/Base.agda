open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Function.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Product.Binary.Base σeq V vs 𝒫

private
  variable
    ℓA ℓB ℓC : Level
    s : S
    A : TheoryTy ℓA s
    B : TheoryTy ℓB s
    C : TheoryTy ℓC s

_⇒_ : ∀ {s} → TheoryTy ℓA s → TheoryTy ℓB s → TheoryTy (ℓ-max ℓA ℓB) s
(A ⇒ B) m = A m → B m

infixr 12 _⇒_

⇒-intro : A & B ⊢ C → A ⊢ B ⇒ C
⇒-intro e m a b = e m (a , b)

⇒-intro⁻ : A ⊢ B ⇒ C → A & B ⊢ C
⇒-intro⁻ f m (a , b) = f m a b

⇒-app : (A ⇒ B) & A ⊢ B
⇒-app m (f , a) = f a

⇒-β : (e : A & B ⊢ C) → ⇒-app ∘⊢ (⇒-intro e ,&p id⊢) ≡ e
⇒-β e = refl

⇒-η : (e : A ⊢ B ⇒ C) → ⇒-intro (⇒-app ∘⊢ (e ,&p id⊢)) ≡ e
⇒-η e = refl
