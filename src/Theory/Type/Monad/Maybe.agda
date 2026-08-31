open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Monad.Maybe
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Top.Base σeq V vs 𝒫
open import Theory.Type.Sum.Binary.Base σeq V vs 𝒫
open import Theory.Type.Product.Binary.Base σeq V vs 𝒫
open import Theory.Type.Monad.Base σeq V vs 𝒫
open import Theory.Type.Monad.Except σeq V vs 𝒫

private variable ℓA ℓB : Level

Maybe : ∀ {s} → TheoryTy ℓA s → TheoryTy ℓA s
Maybe A = Except ⊤Ty A

module _ {s} {A : TheoryTy ℓA s} where
  just : A ⊢ Maybe A
  just = ok ⊤Ty

  nothing : ⊤Ty ⊢ Maybe A
  nothing = throw ⊤Ty

MaybeMonad : Monad
MaybeMonad = ExceptMonad ⊤Ty

module _ {s} {A : TheoryTy ℓA s} where
  orElse : Maybe A & Maybe A ⊢ Maybe A
  orElse = ⊕-elim& (just ∘⊢ π₂) π₁ ∘⊢ &-swap

infixr 5 _∥_
_∥_ : ∀ {s} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  → A ⊢ Maybe B → A ⊢ Maybe B → A ⊢ Maybe B
p ∥ q = orElse ∘⊢ (p ,& q)
