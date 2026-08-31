open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

import Theory.Free.Base as FB
module Theory.Type.HLevels
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Empty as Empty using (⊥*)
open import Cubical.Data.Sigma
import Cubical.Data.Sum as Sum
import Cubical.Data.Equality as Eq
open import Cubical.Data.Unit using (tt* ; isSetUnit ; isSetUnit*)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.FinData using (Fin ; zero ; suc)

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Bottom.Base σeq V vs 𝒫
open import Theory.Type.Top.Base σeq V vs 𝒫
open import Theory.Type.Product.Base σeq V vs 𝒫
open import Theory.Type.Product.Binary.Base σeq V vs 𝒫
open import Theory.Type.Sum.Base σeq V vs 𝒫
open import Theory.Type.Sum.Binary.Base σeq V vs 𝒫
open import Theory.Type.Function.Base σeq V vs 𝒫
open import Theory.Type.Lift.Base σeq V vs 𝒫
open import Theory.Type.Equalizer.Base σeq V vs 𝒫
open import Theory.Type.Operation.Base σeq V vs 𝒫
open import Theory.Type.Residual.Base σeq V vs 𝒫
open import Theory.Type.Monad.Except σeq V vs 𝒫
open import Theory.Type.Monad.Maybe σeq V vs 𝒫
open import Theory.Type.Monad.Cont σeq V vs 𝒫

private variable ℓA ℓB ℓE ℓR ℓY : Level

isSetTheoryTy : ∀ {s} → TheoryTy ℓA s → Type _
isSetTheoryTy A = ∀ m → isSet (A m)

TheorySet : (ℓA : Level) → S → Type (ℓ-max ℓM (ℓ-suc ℓA))
TheorySet ℓA s = Σ[ A ∈ TheoryTy ℓA s ] isSetTheoryTy A

ty : ∀ {s} → TheorySet ℓA s → TheoryTy ℓA s
ty = fst

isSetTy : ∀ {s} (A : TheorySet ℓA s) → isSetTheoryTy (ty A)
isSetTy = snd

isSet⊥Ty : ∀ {s} → isSetTheoryTy (⊥Ty {s = s})
isSet⊥Ty _ = isProp→isSet λ ()

isSet⊤Ty : ∀ {s} → isSetTheoryTy (⊤Ty {s = s})
isSet⊤Ty _ = isSetUnit

isSet⊥Ty↑ : ∀ {s} {ℓB} → isSetTheoryTy (⊥Ty↑ {s = s} ℓB)
isSet⊥Ty↑ _ = isOfHLevelLift 2 (isProp→isSet λ ())

isSet⊤Ty↑ : ∀ {s} {ℓB} → isSetTheoryTy (⊤Ty↑ {s = s} ℓB)
isSet⊤Ty↑ _ = isSetUnit*

isSet&ᴰ : ∀ {s} {Y : Type ℓY} {A : Y → TheoryTy ℓA s}
  → (∀ y → isSetTheoryTy (A y)) → isSetTheoryTy (&ᴰ Y A)
isSet&ᴰ isSetA m = isSetΠ λ y → isSetA y m

isSet⊕ᴰ : ∀ {s} {Y : Type ℓY} {A : Y → TheoryTy ℓA s}
  → isSet Y → (∀ y → isSetTheoryTy (A y)) → isSetTheoryTy (⊕ᴰ Y A)
isSet⊕ᴰ isSetY isSetA m = isSetΣ isSetY λ y → isSetA y m

isSet& : ∀ {s} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  → isSetTheoryTy A → isSetTheoryTy B → isSetTheoryTy (A & B)
isSet& isSetA isSetB m = isSet× (isSetA m) (isSetB m)

isSet⊕ : ∀ {s} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  → isSetTheoryTy A → isSetTheoryTy B → isSetTheoryTy (A ⊕ B)
isSet⊕ isSetA isSetB m = Sum.isSet⊎ (isSetA m) (isSetB m)

_&Set_ : ∀ {s} → TheorySet ℓA s → TheorySet ℓB s → TheorySet (ℓ-max ℓA ℓB) s
(A , sA) &Set (B , sB) = (A & B) , isSet& sA sB

&ᴰSet : ∀ {s} {Y : Type ℓY} → (Y → TheorySet ℓA s) → TheorySet (ℓ-max ℓY ℓA) s
&ᴰSet {Y = Y} A = &ᴰ Y (λ y → ty (A y)) , isSet&ᴰ λ y → A y .snd

⊕ᴰSet : ∀ {s} {Y : Type ℓY} → isSet Y
  → (Y → TheorySet ℓA s) → TheorySet (ℓ-max ℓY ℓA) s
⊕ᴰSet {Y = Y} isSetY A = ⊕ᴰ Y (λ y → ty (A y)) , isSet⊕ᴰ isSetY λ y → A y .snd

_⊕Set_ : ∀ {s} → TheorySet ℓA s → TheorySet ℓB s → TheorySet (ℓ-max ℓA ℓB) s
(A , sA) ⊕Set (B , sB) = (A ⊕ B) , isSet⊕ sA sB

infixr 20 _&Set_
infixr 19 _⊕Set_

isSet⇒ : ∀ {s} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  → isSetTheoryTy B → isSetTheoryTy (A ⇒ B)
isSet⇒ isSetB m = isSetΠ λ _ → isSetB m

isSetLiftTheoryTy : ∀ {s} {A : TheoryTy ℓA s}
  → isSetTheoryTy A → isSetTheoryTy (LiftTheoryTy ℓB A)
isSetLiftTheoryTy isSetA m = isOfHLevelLift 2 (isSetA m)

isSetEqualizer : ∀ {s} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  (f f' : A ⊢ B)
  → isSetTheoryTy A → isSetTheoryTy B → isSetTheoryTy (equalizer f f')
isSetEqualizer f f' isSetA isSetB m =
  isSetΣ (isSetA m) λ x → isProp→isSet (isSetB m (f m x) (f' m x))

isSetResid : ∀ (o : σ .ops) (ℓs : arities σ o → Level)
  (As : Args (σ .arity o) ℓs (σ .sortOf o)) (i : arities σ o)
  {B : TheoryTy ℓB (σ .resultSort o)}
  → isSetTheoryTy B → isSetTheoryTy (Resid o ℓs As i B)
isSetResid o ℓs As i isSetB m =
  isSetΠ λ hs → isSetΠ λ _ → isSetB _

private
  isPropModelEq : ∀ {s} {x y : ↓M s} → isProp (x Eq.≡ y)
  isPropModelEq {s} =
    isOfHLevelRetractFromIso 1 (invIso Eq.PathIsoEq) (M .fst s .snd _ _)

  isSetElems : (n : ℕ) (ℓs : Fin n → Level) (ss : Fin n → S)
    (As : Args n ℓs ss) (ms : (i : Fin n) → ↓M (ss i))
    → ((i : Fin n) → isSet (argAt n ℓs ss As i (ms i)))
    → isSet (Elems n ℓs ss As ms)
  isSetElems zero ℓs ss tt* ms isSetAs = isSetUnit*
  isSetElems (suc n) ℓs ss (A , As) ms isSetAs =
    isSet× (isSetAs zero)
      (isSetElems n (λ i → ℓs (suc i)) (λ i → ss (suc i)) As
        (λ i → ms (suc i)) (λ i → isSetAs (suc i)))

isSet⊗ : ∀ (o : σ .ops) (ℓs : arities σ o → Level)
  (As : Args (σ .arity o) ℓs (σ .sortOf o))
  → ((i : arities σ o) → isSetTheoryTy (argAt (σ .arity o) ℓs (σ .sortOf o) As i))
  → isSetTheoryTy (⊗[ o ][ ℓs ] As)
isSet⊗ o ℓs As isSetAs m =
  isSetΣ (isSetΠ λ a → M .fst (σ .sortOf o a) .snd) λ ms →
  isSet× (isProp→isSet isPropModelEq)
    (isSetElems (σ .arity o) ℓs (σ .sortOf o) As ms
      λ i → isSetAs i (ms i))

isSet⊗ᵘ : ∀ (o : σ .ops) {A : interpIn o (TheoryTy ℓA)}
  → (∀ a → isSetTheoryTy (A a)) → isSetTheoryTy (⊗ᵘ[ o ] A)
isSet⊗ᵘ o isSetA m =
  isSetΣ (isSetΠ λ a → M .fst (σ .sortOf o a) .snd) λ ms →
  isSet× (isProp→isSet isPropModelEq) (isSetΠ λ a → isSetA a (ms a))

isSetExcept : ∀ {s} (E : ∀ {s} → TheoryTy ℓE s) {A : TheoryTy ℓA s}
  → isSetTheoryTy A → isSetTheoryTy E → isSetTheoryTy (Except E A)
isSetExcept E isSetA isSetE = isSet⊕ isSetA isSetE

isSetMaybe : ∀ {s} {A : TheoryTy ℓA s}
  → isSetTheoryTy A → isSetTheoryTy (Maybe A)
isSetMaybe isSetA = isSet⊕ isSetA isSet⊤Ty

isSetCont : ∀ {s} (R : ∀ {s} → TheoryTy ℓR s) {A : TheoryTy ℓA s}
  → isSetTheoryTy R → isSetTheoryTy (Cont R A)
isSetCont R isSetR = isSet⇒ isSetR

-- a proposition at one end of a line of types fills the whole line
isPropPathP : ∀ {ℓ} (T : I → Type ℓ) → isProp (T i0)
  → (x : T i0) (y : T i1) → PathP T x y
isPropPathP T pr =
  isProp→PathP (λ i → transport (λ j → isProp (T (i ∧ j))) pr)
