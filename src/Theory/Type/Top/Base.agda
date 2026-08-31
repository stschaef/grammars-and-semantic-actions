open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Top.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Unit

open import Theory.Base σeq V vs 𝒫

private variable ℓA : Level

⊤Ty : ∀ {s} → TheoryTy ℓ-zero s
⊤Ty _ = Unit

⊤Ty↑ : ∀ {s} ℓB → TheoryTy ℓB s
⊤Ty↑ _ _ = Unit*

module _ {s} {A : TheoryTy ℓA s} where
  ⊤Ty-intro : A ⊢ ⊤Ty
  ⊤Ty-intro _ _ = tt

  ⊤Ty-η : (e : A ⊢ ⊤Ty) → e ≡ ⊤Ty-intro
  ⊤Ty-η e = refl
