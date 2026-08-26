open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Bottom.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Empty as Empty using (⊥*)

open import Theory.Base σeq V vs 𝒫

private variable ℓA : Level

⊥Ty : ∀ {s} → TheoryTy ℓ-zero s
⊥Ty _ = ⊥*

⊥Ty↑ : ∀ {s} ℓB → TheoryTy ℓB s
⊥Ty↑ ℓB w = Lift ℓB (⊥Ty w)

module _ {s} {A : TheoryTy ℓA s} where
  ⊥Ty-elim : ⊥Ty ⊢ A
  ⊥Ty-elim _ ()

  ⊥Ty-η : (e : ⊥Ty ⊢ A) → e ≡ ⊥Ty-elim
  ⊥Ty-η e i _ ()

  -- the same at the lifted empty type, so a client never has to unfold it
  ⊥Ty↑-elim : ∀ {ℓB} → ⊥Ty↑ {s = s} ℓB ⊢ A
  ⊥Ty↑-elim _ ()

  ⊥Ty↑-η : ∀ {ℓB} (e : ⊥Ty↑ {s = s} ℓB ⊢ A) → e ≡ ⊥Ty↑-elim
  ⊥Ty↑-η e i _ ()
