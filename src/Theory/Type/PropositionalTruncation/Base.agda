-- Propositional truncation, pointwise.  `∥ A ∥` is the largest unambiguous
-- quotient of `A`: it remembers which elements `A` has and forgets how many.
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.WildCat.LocallySmall.Base
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.PropositionalTruncation.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Sigma

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Top.Base σeq V vs 𝒫
open import Theory.Type.HLevels σeq V vs 𝒫
open import Theory.Type.Product.Binary.Base σeq V vs 𝒫
open import Theory.Type.Unambiguity.Base σeq V vs 𝒫
open import Theory.Type.Equivalence.Base σeq V vs 𝒫
open import Theory.Type.Subtype.Base σeq V vs 𝒫

open WildCatNotation
open WildCatIso

private variable ℓA ℓB : Level

∥_∥ : ∀ {s} → TheoryTy ℓA s → TheoryTy ℓA s
∥ A ∥ m = PT.∥ A m ∥₁

trunc : ∀ {s} {A : TheoryTy ℓA s} → A ⊢ ∥ A ∥
trunc _ x = PT.∣ x ∣₁

unambiguous∥∥ : ∀ {s} {A : TheoryTy ℓA s} → unambiguous ∥ A ∥
unambiguous∥∥ _ = PT.isPropPropTrunc

isSet∥∥ : ∀ {s} {A : TheoryTy ℓA s} → isSetTheoryTy ∥ A ∥
isSet∥∥ m = isProp→isSet PT.isPropPropTrunc

-- The universal property: `∥_∥` is left adjoint to the inclusion of the
-- unambiguous types.  In `Theory`, `unambiguous A = ∀ m → isProp (A m)`, so
-- this is `PT.rec` with nothing in the way.
elim∥∥ : ∀ {s} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  → unambiguous A → B ⊢ A → ∥ B ∥ ⊢ A
elim∥∥ unambig-A f m = PT.rec (unambig-A m) (f m)

∥∥-map : ∀ {s} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  → A ⊢ B → ∥ A ∥ ⊢ ∥ B ∥
∥∥-map f = elim∥∥ unambiguous∥∥ (trunc ∘⊢ f)

∥∥idem : ∀ {s} {A : TheoryTy ℓA s} → unambiguous A → A ≅ ∥ A ∥
∥∥idem unambig-A .fun = trunc
∥∥idem unambig-A .inv = elim∥∥ unambig-A id⊢
∥∥idem unambig-A .sec = unambiguous→subterminal unambiguous∥∥ _ _
∥∥idem unambig-A .ret = unambiguous→subterminal unambig-A _ _

-- The subobject of `A` at which some `B` parse exists over the same element.
-- This is the image factorisation's middle object when `f : B ⊢ A`.
module ∃SubTy {s : S} (A : TheoryTy ℓA s) (B : TheoryTy ℓB s) where
  ∃-prop : A ⊢ Ω {ℓ' = ℓB}
  ∃-prop = unambiguous-prop (unambiguous∥∥ {A = B}) A

  ∃subTy : TheoryTy (ℓ-max ℓA ℓB) s
  ∃subTy = subTy ∃-prop

  ∃-π : ∃subTy ⊢ A
  ∃-π = sub-π ∃-prop

  witness∃ : ∃subTy ⊢ ∥ B ∥
  witness∃ = extract-pf ∃-prop ∃-π (sub-π-pf ∃-prop)

  witness∃' : ∃subTy ⊢ A & ∥ B ∥
  witness∃' = ∃-π ,& witness∃

  -- The image factorisation: any map into `A` that has a `B` over it
  -- factors through the subobject.
  ∃-intro : {C : TheoryTy ℓA s} (f : C ⊢ A) → C ⊢ ∥ B ∥ → C ⊢ ∃subTy
  ∃-intro f g = sub-intro ∃-prop f (insert-pf ∃-prop f λ m x → g m x)
