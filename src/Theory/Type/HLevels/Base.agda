open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

import Theory.Free.Base as FB
module Theory.Type.HLevels.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Sigma

open import Theory.Base σeq V vs 𝒫

private variable ℓA : Level

isSetTheoryTy : ∀ {s} → TheoryTy ℓA s → Type _
isSetTheoryTy A = ∀ m → isSet (A m)

TheorySet : (ℓA : Level) → S → Type (ℓ-max ℓM (ℓ-suc ℓA))
TheorySet ℓA s = Σ[ A ∈ TheoryTy ℓA s ] isSetTheoryTy A

ty : ∀ {s} → TheorySet ℓA s → TheoryTy ℓA s
ty = fst

isSetTy : ∀ {s} (A : TheorySet ℓA s) → isSetTheoryTy (ty A)
isSetTy = snd
