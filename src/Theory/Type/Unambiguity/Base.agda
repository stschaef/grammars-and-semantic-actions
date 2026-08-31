open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Unambiguity.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Representable.Base σeq V vs 𝒫
open import Theory.Type.Top.Base σeq V vs 𝒫
open import Theory.Type.Bottom.Base σeq V vs 𝒫
open import Theory.Type.Product.Binary.Base σeq V vs 𝒫
open import Theory.Type.Function.Base σeq V vs 𝒫

private variable ℓA ℓB ℓC : Level

unambiguous : {s : S} → TheoryTy ℓA s → Type _
unambiguous A = ∀ m → isProp (A m)

subterminal : {s : S} → TheoryTy ℓA s → Typeω
subterminal A = ∀ {ℓB} {B : TheoryTy ℓB _} (f g : B ⊢ A) → f ≡ g

unambiguous→subterminal : {s : S} {A : TheoryTy ℓA s}
  → unambiguous A → subterminal A
unambiguous→subterminal p f g = funExt λ m → funExt λ x → p m (f m x) (g m x)

subterminal→unambiguous : {s : S} {A : TheoryTy ℓA s}
  → subterminal A → unambiguous A
subterminal→unambiguous {A = A} u m x y =
  cong (λ f → f m Eq.refl) (u to-x to-y)
  where
  to-x : ⌈ m ⌉ ⊢ A
  to-x m' Eq.refl = x
  to-y : ⌈ m ⌉ ⊢ A
  to-y m' Eq.refl = y

unambiguous⊤ : {s : S} → unambiguous (⊤Ty {s = s})
unambiguous⊤ m x y = refl

unambiguous⊥ : {s : S} → unambiguous (⊥Ty {s = s})
unambiguous⊥ m ()

&unambiguous : {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  → unambiguous A → unambiguous B → unambiguous (A & B)
&unambiguous uA uB m = isProp× (uA m) (uB m)

unambiguous⇒ : {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  → unambiguous B → unambiguous (A ⇒ B)
unambiguous⇒ uB m = isProp→ (uB m)

unambiguousRetract : {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  (f : A ⊢ B) (g : B ⊢ A) → g ∘⊢ f ≡ id⊢
  → unambiguous B → unambiguous A
unambiguousRetract f g sec uB m x y =
  sym (funExt⁻ (funExt⁻ sec m) x)
  ∙ cong (g m) (uB m (f m x) (f m y))
  ∙ funExt⁻ (funExt⁻ sec m) y
