-- TODO how much of this actually used?
-- WARNING for now I have been treating this as a place to sequester the
-- semantic reasoning about guarded recursion so that importers of this
-- module can work with a clean interface
-- The implementation are subject to change per experiments w Cass
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Later.Derivative
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Residual.Base σeq V vs 𝒫 public

private variable ℓA ℓB : Level

Derivative : {s t : S} → (↓M s → ↓M t) → TheoryTy ℓA t → TheoryTy ℓA s
Derivative f B m = B (f m)

√ : {s t : S} → (↓M s → ↓M t) → TheoryTy ℓA s → TheoryTy _ t
√ f A z = (m : ↓M _) → f m Eq.≡ z → A m

√-intro : {s t : S} (f : ↓M s → ↓M t)
  {A : TheoryTy ℓA s} {B : TheoryTy ℓB t}
  → Derivative f B ⊢ A → B ⊢ √ f A
√-intro f {B = B} e z b m p =
  e m (subst⁻ B (Eq.eqToPath p) b)

√-intro⁻ : {s t : S} (f : ↓M s → ↓M t)
  {A : TheoryTy ℓA s} {B : TheoryTy ℓB t}
  → B ⊢ √ f A → Derivative f B ⊢ A
√-intro⁻ f e m b = e (f m) b m Eq.refl

√-β : {s t : S} (f : ↓M s → ↓M t)
  {A : TheoryTy ℓA s} {B : TheoryTy ℓB t}
  (e : Derivative f B ⊢ A)
  → √-intro⁻ f {A = A} {B = B} (√-intro f {A = A} {B = B} e) ≡ e
√-β f {A = A} {B = B} e = funExt λ m → funExt λ b →
  cong (e m) (transportRefl b)

√-η : {s t : S} (f : ↓M s → ↓M t)
  {A : TheoryTy ℓA s} {B : TheoryTy ℓB t}
  (e : B ⊢ √ f A)
  → √-intro f {A = A} {B = B} (√-intro⁻ f {A = A} {B = B} e) ≡ e
√-η f {A = A} {B = B} e = funExt λ z → funExt λ b → funExt λ m → funExt λ where
  Eq.refl → cong (λ b' → e (f m) b' m Eq.refl) (transportRefl b)

√Iso : {s t : S} (f : ↓M s → ↓M t)
  {A : TheoryTy ℓA s} {B : TheoryTy ℓB t}
  → Iso (Derivative f B ⊢ A) (B ⊢ √ f A)
√Iso f {A = A} {B = B} .Iso.fun = √-intro f {A = A} {B = B}
√Iso f {A = A} {B = B} .Iso.inv = √-intro⁻ f {A = A} {B = B}
√Iso f {A = A} {B = B} .Iso.sec = √-η f {A = A} {B = B}
√Iso f {A = A} {B = B} .Iso.ret = √-β f {A = A} {B = B}

DerivativeAt : (o : σ .ops) (i : arities σ o)
  → HoleVals (σ .arity o) (σ .sortOf o) i
  → TheoryTy ℓA (σ .resultSort o) → TheoryTy ℓA (σ .sortOf o i)
DerivativeAt o i hs = Derivative (λ m →
  op o (fillVals (σ .arity o) (σ .sortOf o) i hs m))

√At : (o : σ .ops) (i : arities σ o)
  → HoleVals (σ .arity o) (σ .sortOf o) i
  → TheoryTy ℓA (σ .sortOf o i) → TheoryTy _ (σ .resultSort o)
√At o i hs = √ (λ m →
  op o (fillVals (σ .arity o) (σ .sortOf o) i hs m))

√AtIso : (o : σ .ops) (i : arities σ o)
  (hs : HoleVals (σ .arity o) (σ .sortOf o) i)
  {A : TheoryTy ℓA (σ .sortOf o i)} {B : TheoryTy ℓB (σ .resultSort o)}
  → Iso (DerivativeAt o i hs B ⊢ A) (B ⊢ √At o i hs A)
√AtIso o i hs = √Iso (λ m →
  op o (fillVals (σ .arity o) (σ .sortOf o) i hs m))
