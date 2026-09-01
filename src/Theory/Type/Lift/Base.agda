open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Lift.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Theory.Base σeq V vs 𝒫

private
  variable
    ℓA ℓB ℓC ℓD : Level

LiftTheoryTy : ∀ {s} ℓB → TheoryTy ℓA s → TheoryTy (ℓ-max ℓA ℓB) s
LiftTheoryTy ℓB A w = Lift ℓB (A w)

liftTy : ∀ {s} {A : TheoryTy ℓA s} → A ⊢ LiftTheoryTy ℓB A
liftTy = λ w z → lift z

lowerTy : ∀ {s} {A : TheoryTy ℓA s} → LiftTheoryTy ℓB A ⊢ A
lowerTy = λ w z → z .lower
