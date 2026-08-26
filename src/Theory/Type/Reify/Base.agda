-- Reifying a predicate on the carrier as a type: `Reify P` is inhabited at
-- `m` exactly when `P m` is, and by nothing else.
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Reify.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Sum.Base σeq V vs 𝒫
open import Theory.Type.Representable.Base σeq V vs 𝒫

private variable ℓA : Level

module _ {s : S} (P : ↓M s → Type ℓA) where
  Reify : TheoryTy (ℓ-max ℓM ℓA) s
  Reify = ⊕[ m ∈ ↓M s ] ⊕[ _ ∈ P m ] ⌈ m ⌉
