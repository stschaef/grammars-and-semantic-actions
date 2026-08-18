open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Equality as Eq
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Representable.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Theory.Base σeq V vs 𝒫

open Iso

private variable ℓA ℓA' ℓB : Level

-- Yoneda: a map out of a representable is a point
yoIso : ∀ {s} {A : TheoryTy ℓA s} (m : ↓M s) → Iso (⌈ m ⌉ ⊢ A) (A m)
yoIso m .fun f = f m Eq.refl
yoIso m .inv a m' Eq.refl = a
yoIso m .sec a = refl
yoIso m .ret f = funExt λ m' → funExt λ where Eq.refl → refl

-- precomposition with a pointwise iso
precompIso : ∀ {s} {A : TheoryTy ℓA s} {A' : TheoryTy ℓA' s}
  {B : TheoryTy ℓB s}
  → (∀ m → Iso (A m) (A' m)) → Iso (A ⊢ B) (A' ⊢ B)
precompIso e .fun f m x = f m (e m .inv x)
precompIso e .inv g m x = g m (e m .fun x)
precompIso e .sec g = funExt λ m → funExt λ x → cong (g m) (e m .sec x)
precompIso e .ret f = funExt λ m → funExt λ x → cong (f m) (e m .ret x)
