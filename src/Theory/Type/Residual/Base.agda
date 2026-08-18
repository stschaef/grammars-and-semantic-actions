-- This is an attempt to give a uniform defintion of residuals
-- for all theories at once. It's not definitonally that nice, say for
-- the η-law, unless stating the adjunction with respect to the focused
-- version of ⊗
-- It tentatively seems that a manual definition of residuals
-- for each theory is the best definitionally, but perhaps there
-- is someway to clean this up to recover those niceties in general
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Foundations.Isomorphism
open import Cubical.WildCat.LocallySmall.Base
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Residual.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Operation.Base σeq V vs 𝒫

open WildCatNotation
open WildCatIso

open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.FinData using (Fin ; zero ; suc)

private variable ℓB : Level


-- The values in every slot except the focused one.  Unlike `HoleElems`,
-- this is independent of a full tuple: filling it computes that tuple.
HoleVals : (n : ℕ) (ss : Fin n → S) (i : Fin n) → Type ℓM
HoleVals zero ss ()
HoleVals (suc n) ss zero = (j : Fin n) → ↓M (ss (suc j))
HoleVals (suc n) ss (suc i) =
  ↓M (ss zero) × HoleVals n (λ j → ss (suc j)) i

fillVals : (n : ℕ) (ss : Fin n → S) (i : Fin n)
  → HoleVals n ss i → ↓M (ss i) → (a : Fin n) → ↓M (ss a)
fillVals (suc n) ss zero hs x zero = x
fillVals (suc n) ss zero hs x (suc a) = hs a
fillVals (suc n) ss (suc i) (x , hs) y zero = x
fillVals (suc n) ss (suc i) (x , hs) y (suc a) =
  fillVals n (λ j → ss (suc j)) i hs y a

fillVals-at : (n : ℕ) (ss : Fin n → S) (i : Fin n)
  (hs : HoleVals n ss i) (m : ↓M (ss i))
  → fillVals n ss i hs m i ≡ m
fillVals-at (suc n) ss zero hs m = refl
fillVals-at (suc n) ss (suc i) (x , hs) m =
  fillVals-at n (λ j → ss (suc j)) i hs m

removeVals : (n : ℕ) (ss : Fin n → S) (i : Fin n)
  → ((a : Fin n) → ↓M (ss a)) → HoleVals n ss i
removeVals (suc n) ss zero ms = λ a → ms (suc a)
removeVals (suc n) ss (suc i) ms =
  ms zero , removeVals n (λ a → ss (suc a)) i (λ a → ms (suc a))

fill-removeVals : (n : ℕ) (ss : Fin n → S) (i : Fin n)
  (ms : (a : Fin n) → ↓M (ss a))
  → fillVals n ss i (removeVals n ss i ms) (ms i) ≡ ms
fill-removeVals (suc n) ss zero ms = funExt λ where
  zero → refl
  (suc a) → refl
fill-removeVals (suc n) ss (suc i) ms = funExt λ where
    zero → refl
    (suc a) → cong (λ fs → fs a)
      (fill-removeVals n (λ b → ss (suc b)) i (λ b → ms (suc b)))

remove-fillVals : (n : ℕ) (ss : Fin n → S) (i : Fin n)
  (hs : HoleVals n ss i) (m : ↓M (ss i))
  → removeVals n ss i (fillVals n ss i hs m) ≡ hs
remove-fillVals (suc n) ss zero hs m = funExt λ where
  zero → refl
  (suc a) → refl
remove-fillVals (suc n) ss (suc i) (x , hs) m =
  cong (λ zs → x , zs)
    (remove-fillVals n (λ a → ss (suc a)) i hs m)

focusedValsIso : (n : ℕ) (ss : Fin n → S) (i : Fin n)
  → Iso (Σ[ hs ∈ HoleVals n ss i ] ↓M (ss i))
        ((a : Fin n) → ↓M (ss a))
focusedValsIso n ss i .Iso.fun (hs , m) = fillVals n ss i hs m
focusedValsIso n ss i .Iso.inv ms = removeVals n ss i ms , ms i
focusedValsIso n ss i .Iso.sec ms = fill-removeVals n ss i ms
focusedValsIso n ss i .Iso.ret (hs , m) =
  ΣPathP (remove-fillVals n ss i hs m ,
    toPathP (transportRefl _ ∙ fillVals-at n ss i hs m))

HoleElems : (n : ℕ) (ℓs : Fin n → Level) (ss : Fin n → S)
  (As : Args n ℓs ss) (i : Fin n) → ((a : Fin n) → ↓M (ss a)) → Type (sup n ℓs)
HoleElems zero ℓs ss As () ms
HoleElems (suc n) ℓs ss (A , As) zero ms =
  Lift (ℓs zero)
    (Elems n (λ a → ℓs (suc a)) (λ a → ss (suc a)) As (λ a → ms (suc a)))
HoleElems (suc n) ℓs ss (A , As) (suc i) ms =
  A (ms zero) × HoleElems n (λ a → ℓs (suc a)) (λ a → ss (suc a)) As i
    (λ a → ms (suc a))

fillElems : (n : ℕ) (ℓs : Fin n → Level) (ss : Fin n → S)
  (As : Args n ℓs ss) (i : Fin n) (ms : (a : Fin n) → ↓M (ss a))
  → HoleElems n ℓs ss As i ms → argAt n ℓs ss As i (ms i)
  → Elems n ℓs ss As ms
fillElems (suc n) ℓs ss (A , As) zero ms hs x = x , hs .lower
fillElems (suc n) ℓs ss (A , As) (suc i) ms (x , hs) y =
  x , fillElems n (λ a → ℓs (suc a)) (λ a → ss (suc a)) As i
        (λ a → ms (suc a)) hs y

removeElems : (n : ℕ) (ℓs : Fin n → Level) (ss : Fin n → S)
  (As : Args n ℓs ss) (i : Fin n) (ms : (a : Fin n) → ↓M (ss a))
  → Elems n ℓs ss As ms → HoleElems n ℓs ss As i ms
removeElems (suc n) ℓs ss (A , As) zero ms (x , xs) = lift xs
removeElems (suc n) ℓs ss (A , As) (suc i) ms (x , xs) =
  x , removeElems n (λ a → ℓs (suc a)) (λ a → ss (suc a)) As i
        (λ a → ms (suc a)) xs

fill-remove : (n : ℕ) (ℓs : Fin n → Level) (ss : Fin n → S)
  (As : Args n ℓs ss) (i : Fin n) (ms : (a : Fin n) → ↓M (ss a))
  (xs : Elems n ℓs ss As ms)
  → fillElems n ℓs ss As i ms (removeElems n ℓs ss As i ms xs)
      (elemAt n ℓs ss As ms xs i) ≡ xs
fill-remove (suc n) ℓs ss (A , As) zero ms (x , xs) = refl
fill-remove (suc n) ℓs ss (A , As) (suc i) ms (x , xs) =
  cong (λ ys → x , ys)
    (fill-remove n (λ a → ℓs (suc a)) (λ a → ss (suc a)) As i
      (λ a → ms (suc a)) xs)

elem-fill : (n : ℕ) (ℓs : Fin n → Level) (ss : Fin n → S)
  (As : Args n ℓs ss) (i : Fin n) (ms : (a : Fin n) → ↓M (ss a))
  (hs : HoleElems n ℓs ss As i ms) (x : argAt n ℓs ss As i (ms i))
  → elemAt n ℓs ss As ms (fillElems n ℓs ss As i ms hs x) i ≡ x
elem-fill (suc n) ℓs ss (A , As) zero ms hs x = refl
elem-fill (suc n) ℓs ss (A , As) (suc i) ms (x , hs) y =
  elem-fill n (λ a → ℓs (suc a)) (λ a → ss (suc a)) As i
    (λ a → ms (suc a)) hs y

remove-fill : (n : ℕ) (ℓs : Fin n → Level) (ss : Fin n → S)
  (As : Args n ℓs ss) (i : Fin n) (ms : (a : Fin n) → ↓M (ss a))
  (hs : HoleElems n ℓs ss As i ms) (x : argAt n ℓs ss As i (ms i))
  → removeElems n ℓs ss As i ms (fillElems n ℓs ss As i ms hs x) ≡ hs
remove-fill (suc n) ℓs ss (A , As) zero ms hs x = refl
remove-fill (suc n) ℓs ss (A , As) (suc i) ms (x , hs) y =
  cong (λ zs → x , zs)
    (remove-fill n (λ a → ℓs (suc a)) (λ a → ss (suc a)) As i
      (λ a → ms (suc a)) hs y)

focusedElemsIso : (n : ℕ) (ℓs : Fin n → Level) (ss : Fin n → S)
  (As : Args n ℓs ss) (i : Fin n) (hs : HoleVals n ss i) (m : ↓M (ss i))
  → Iso (HoleElems n ℓs ss As i (fillVals n ss i hs m) × argAt n ℓs ss As i m)
        (Elems n ℓs ss As (fillVals n ss i hs m))
focusedElemsIso n ℓs ss As i hs m .Iso.fun (ys , x) =
  fillElems n ℓs ss As i (fillVals n ss i hs m) ys
    (subst⁻ (argAt n ℓs ss As i) (fillVals-at n ss i hs m) x)
focusedElemsIso n ℓs ss As i hs m .Iso.inv xs =
  removeElems n ℓs ss As i filled xs ,
  subst (argAt n ℓs ss As i) at (elemAt n ℓs ss As filled xs i)
  where
  filled = fillVals n ss i hs m
  at = fillVals-at n ss i hs m
focusedElemsIso n ℓs ss As i hs m .Iso.sec xs =
  cong (fillElems n ℓs ss As i filled (removeElems n ℓs ss As i filled xs))
    (subst⁻Subst (argAt n ℓs ss As i) at (elemAt n ℓs ss As filled xs i))
  ∙ fill-remove n ℓs ss As i filled xs
  where
  filled = fillVals n ss i hs m
  at = fillVals-at n ss i hs m
focusedElemsIso n ℓs ss As i hs m .Iso.ret (ys , x) =
  ΣPathP (remove-fill n ℓs ss As i filled ys x' ,
    toPathP (transportRefl _ ∙
      cong (subst (argAt n ℓs ss As i) at)
        (elem-fill n ℓs ss As i filled ys x')
      ∙ substSubst⁻ (argAt n ℓs ss As i) at x))
  where
  filled = fillVals n ss i hs m
  at = fillVals-at n ss i hs m
  x' = subst⁻ (argAt n ℓs ss As i) at x

Resid : (o : σ .ops) (ℓs : arities σ o → Level)
  (As : Args (σ .arity o) ℓs (σ .sortOf o)) (i : arities σ o)
  (B : TheoryTy ℓB (σ .resultSort o)) → TheoryTy _ (σ .sortOf o i)
Resid o ℓs As i B m =
  (hs : HoleVals (σ .arity o) (σ .sortOf o) i) →
  HoleElems (σ .arity o) ℓs (σ .sortOf o) As i
    (fillVals (σ .arity o) (σ .sortOf o) i hs m) →
  B (op o (fillVals (σ .arity o) (σ .sortOf o) i hs m))

syntax Resid o ℓs As i B = As ⊸⟨ o [ ℓs ] at i ⟩ B

FocusedOperation : (o : σ .ops) (ℓs : arities σ o → Level)
  (As : Args (σ .arity o) ℓs (σ .sortOf o)) (i : arities σ o)
  → TheoryTy _ (σ .resultSort o)
FocusedOperation o ℓs As i z =
  Σ[ hs ∈ HoleVals (σ .arity o) (σ .sortOf o) i ]
  Σ[ m ∈ ↓M (σ .sortOf o i) ]
  (op o (fillVals (σ .arity o) (σ .sortOf o) i hs m) Eq.≡ z) ×
  (HoleElems (σ .arity o) ℓs (σ .sortOf o) As i
   (fillVals (σ .arity o) (σ .sortOf o) i hs m) ×
   argAt (σ .arity o) ℓs (σ .sortOf o) As i m)

focusedOperationIso : (o : σ .ops) (ℓs : arities σ o → Level)
  (As : Args (σ .arity o) ℓs (σ .sortOf o)) (i : arities σ o)
  (z : ↓M (σ .resultSort o))
  → Iso (FocusedOperation o ℓs As i z) (⊗[ o ][ ℓs ] As z)
focusedOperationIso o ℓs As i z =
  compIso (invIso Σ-assoc-Iso)
    (compIso
      (Σ-cong-iso-snd λ hs-m →
        Σ-cong-iso-snd λ p →
          focusedElemsIso (σ .arity o) ℓs (σ .sortOf o) As i
            (hs-m .fst) (hs-m .snd))
      (Σ-cong-iso (focusedValsIso (σ .arity o) (σ .sortOf o) i)
        (λ hs-m → idIso)))

FocusedOperation≅⊗ : (o : σ .ops) (ℓs : arities σ o → Level)
  (As : Args (σ .arity o) ℓs (σ .sortOf o)) (i : arities σ o)
  → FocusedOperation o ℓs As i ≅ ⊗[ o ][ ℓs ] As
FocusedOperation≅⊗ o ℓs As i .fun z = focusedOperationIso o ℓs As i z .Iso.fun
FocusedOperation≅⊗ o ℓs As i .inv z = focusedOperationIso o ℓs As i z .Iso.inv
FocusedOperation≅⊗ o ℓs As i .sec = funExt λ z →
  funExt λ q → focusedOperationIso o ℓs As i z .Iso.sec q
FocusedOperation≅⊗ o ℓs As i .ret = funExt λ z →
  funExt λ q → focusedOperationIso o ℓs As i z .Iso.ret q

module _ (o : σ .ops) (ℓs : arities σ o → Level)
  (As : Args (σ .arity o) ℓs (σ .sortOf o)) (i : arities σ o) where

  focused-⊸-intro : {B : TheoryTy ℓB (σ .resultSort o)}
    → FocusedOperation o ℓs As i ⊢ B
    → argAt (σ .arity o) ℓs (σ .sortOf o) As i ⊢ As ⊸⟨ o [ ℓs ] at i ⟩ B
  focused-⊸-intro e m x hs ys =
    e (op o (fillVals (σ .arity o) (σ .sortOf o) i hs m))
      (hs , m , Eq.refl , ys , x)

  focused-⊸-intro⁻ : {B : TheoryTy ℓB (σ .resultSort o)}
    → argAt (σ .arity o) ℓs (σ .sortOf o) As i ⊢ As ⊸⟨ o [ ℓs ] at i ⟩ B
    → FocusedOperation o ℓs As i ⊢ B
  focused-⊸-intro⁻ e z (hs , m , Eq.refl , ys , x) = e m x hs ys

  focused-⊸-η : {B : TheoryTy ℓB (σ .resultSort o)}
    (e : argAt (σ .arity o) ℓs (σ .sortOf o) As i ⊢ As ⊸⟨ o [ ℓs ] at i ⟩ B)
    → focused-⊸-intro {B = B} (focused-⊸-intro⁻ {B = B} e) ≡ e
  focused-⊸-η e = refl

  focused-⊸-β : {B : TheoryTy ℓB (σ .resultSort o)}
    (e : FocusedOperation o ℓs As i ⊢ B)
    → focused-⊸-intro⁻ {B = B} (focused-⊸-intro {B = B} e) ≡ e
  focused-⊸-β e = funExt λ z → funExt λ where
    (hs , m , Eq.refl , ys , x) → refl

  ⊸-intro : {B : TheoryTy ℓB (σ .resultSort o)}
    → ⊗[ o ][ ℓs ] As ⊢ B
    → argAt (σ .arity o) ℓs (σ .sortOf o) As i ⊢ As ⊸⟨ o [ ℓs ] at i ⟩ B
  ⊸-intro {B = B} e = focused-⊸-intro {B = B} λ z q →
    e z (focusedOperationIso o ℓs As i z .Iso.fun q)

  ⊸-intro⁻ : {B : TheoryTy ℓB (σ .resultSort o)}
    → argAt (σ .arity o) ℓs (σ .sortOf o) As i ⊢ As ⊸⟨ o [ ℓs ] at i ⟩ B
    → ⊗[ o ][ ℓs ] As ⊢ B
  ⊸-intro⁻ {B = B} e z q = focused-⊸-intro⁻ {B = B} e z
    (focusedOperationIso o ℓs As i z .Iso.inv q)

  ⊸-β : {B : TheoryTy ℓB (σ .resultSort o)}
    (e : ⊗[ o ][ ℓs ] As ⊢ B)
    → ⊸-intro⁻ {B = B} (⊸-intro {B = B} e) ≡ e
  ⊸-β {B = B} e = funExt λ z → funExt λ q →
    cong (λ f → f z (focusedOperationIso o ℓs As i z .Iso.inv q))
      (focused-⊸-β {B = B} (λ z p →
        e z (focusedOperationIso o ℓs As i z .Iso.fun p)))
    ∙ cong (e z) (focusedOperationIso o ℓs As i z .Iso.sec q)

  ⊸-η : {B : TheoryTy ℓB (σ .resultSort o)}
    (e : argAt (σ .arity o) ℓs (σ .sortOf o) As i ⊢ As ⊸⟨ o [ ℓs ] at i ⟩ B)
    → ⊸-intro {B = B} (⊸-intro⁻ {B = B} e) ≡ e
  ⊸-η {B = B} e = funExt λ m → funExt λ x → funExt λ hs → funExt λ ys →
    cong (focused-⊸-intro⁻ {B = B} e
      (op o (fillVals (σ .arity o) (σ .sortOf o) i hs m)))
      (focusedOperationIso o ℓs As i
        (op o (fillVals (σ .arity o) (σ .sortOf o) i hs m)) .Iso.ret
        (hs , m , Eq.refl , ys , x))
    ∙ cong (λ f → f m x hs ys) (focused-⊸-η {B = B} e)

  ⊸Iso : {B : TheoryTy ℓB (σ .resultSort o)}
    → Iso (⊗[ o ][ ℓs ] As ⊢ B)
          (argAt (σ .arity o) ℓs (σ .sortOf o) As i ⊢ As ⊸⟨ o [ ℓs ] at i ⟩ B)
  ⊸Iso {B = B} .Iso.fun = ⊸-intro {B = B}
  ⊸Iso {B = B} .Iso.inv = ⊸-intro⁻ {B = B}
  ⊸Iso {B = B} .Iso.sec = ⊸-η {B = B}
  ⊸Iso {B = B} .Iso.ret = ⊸-β {B = B}
