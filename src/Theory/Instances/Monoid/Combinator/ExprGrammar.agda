{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The expression grammar  E → E + T | T    T → ( E ) | x
   shared by `Ascent/Expr` and `LeftCorner/Expr`.  Nothing here parses. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.ExprGrammar where

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)

data Tk : Type where
  ‵x ‵+ ‵lp ‵rp : Tk

_≟K_ : (x y : Tk) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
‵x ≟K ‵x = Sum.inl Eq.refl
‵+ ≟K ‵+ = Sum.inl Eq.refl
‵lp ≟K ‵lp = Sum.inl Eq.refl
‵rp ≟K ‵rp = Sum.inl Eq.refl
‵x ≟K ‵+ = Sum.inr λ ()
‵x ≟K ‵lp = Sum.inr λ ()
‵x ≟K ‵rp = Sum.inr λ ()
‵+ ≟K ‵x = Sum.inr λ ()
‵+ ≟K ‵lp = Sum.inr λ ()
‵+ ≟K ‵rp = Sum.inr λ ()
‵lp ≟K ‵x = Sum.inr λ ()
‵lp ≟K ‵+ = Sum.inr λ ()
‵lp ≟K ‵rp = Sum.inr λ ()
‵rp ≟K ‵x = Sum.inr λ ()
‵rp ≟K ‵+ = Sum.inr λ ()
‵rp ≟K ‵lp = Sum.inr λ ()

open import Theory.Instances.Monoid.Combinator.Core Tk _≟K_
open import Theory.Instances.Monoid.Residual Tk isSetAlphabet
  using (⟦⊗e⟧ ; ⟦⊗e⟧⁻)

infixr 20 _`⊗_
_`⊗_ : {X : Type ℓ-zero} → Functor ℓM X (λ _ → tt) tt
     → Functor ℓM X (λ _ → tt) tt → Functor ℓM X (λ _ → tt) tt
F `⊗ G = ⊗e _⊙_ (two F G)

isSet`⊗ : {X : Type ℓ-zero} {F G : Functor ℓM X (λ _ → tt) tt}
  → isSetValued F → isSetValued G → isSetValued (F `⊗ G)
isSet`⊗ sF sG zero = sF
isSet`⊗ sF sG (suc zero) = sG

‵lit : {X : Type ℓ-zero} → Tk → Functor ℓM X (λ _ → tt) tt
‵lit c = k (literal c)

isLit : (X : Type ℓ-zero) (c : Tk)
  → isSetValued {ℓA = ℓM} {X = X} {xs = λ _ → tt} (‵lit c)
isLit X c = lift (isSetLiteral c)

isVar : (X : Type ℓ-zero) (x : X)
  → isSetValued {ℓA = ℓM} {X = X} {xs = λ _ → tt} (Var x)
isVar X x = lift tt*

isEps : (X : Type ℓ-zero)
  → isSetValued {ℓA = ℓM} {X = X} {xs = λ _ → tt} (k εTy)
isEps X = lift isSetεTy

data NT : Type where
  nE nT : NT

-- `G` is exactly the shape `Derivative/Parser` takes, so it is public.
Gbr : NT → Bool → Functor ℓM NT (λ _ → tt) tt
Gbr nE false = Var nE `⊗ (‵lit ‵+ `⊗ Var nT)
Gbr nE true  = Var nT
Gbr nT false = ‵lit ‵lp `⊗ (Var nE `⊗ ‵lit ‵rp)
Gbr nT true  = ‵lit ‵x

G : NT → Functor ℓM NT (λ _ → tt) tt
G x = ⊕e Bool (Gbr x)

private

  isSetGbr : (x : NT) (b : Bool) → isSetValued (Gbr x b)
  isSetGbr nE false = isSet`⊗ (isVar NT nE) (isSet`⊗ (isLit NT ‵+) (isVar NT nT))
  isSetGbr nE true  = isVar NT nT
  isSetGbr nT false = isSet`⊗ (isLit NT ‵lp) (isSet`⊗ (isVar NT nE) (isLit NT ‵rp))
  isSetGbr nT true  = isLit NT ‵x

  isSetG : (x : NT) → isSetValued (G x)
  isSetG x .fst = lift isSetBool
  isSetG x .snd = isSetGbr x

E : TheoryTy _ tt
E = μ G nE

Trm : TheoryTy _ tt
Trm = μ G nT

Eset : TheorySet _ tt
Eset = E , isSetμ G isSetG nE

-- the productions, as the terms `reduce` fires
addE : E ⊗ (literal ‵+ ⊗ Trm) ⊢ E
addE = roll ∘⊢ σ⊕ false
  ∘⊢ ⟦⊗e⟧⁻ (Var nE) (‵lit ‵+ `⊗ Var nT)
  ∘⊢ (liftTy ,⊗ (⟦⊗e⟧⁻ (‵lit ‵+) (Var nT) ∘⊢ (liftTy ,⊗ liftTy)))

embE : Trm ⊢ E
embE = roll ∘⊢ σ⊕ true ∘⊢ liftTy

parT : literal ‵lp ⊗ (E ⊗ literal ‵rp) ⊢ Trm
parT = roll ∘⊢ σ⊕ false
  ∘⊢ ⟦⊗e⟧⁻ (‵lit ‵lp) (Var nE `⊗ ‵lit ‵rp)
  ∘⊢ (liftTy ,⊗ (⟦⊗e⟧⁻ (Var nE) (‵lit ‵rp) ∘⊢ (liftTy ,⊗ liftTy)))

varT : literal ‵x ⊢ Trm
varT = roll ∘⊢ σ⊕ true ∘⊢ liftTy

-- the readout into ordinary datatypes

data Ex : Type
data Fac : Type

data Ex where
  add : Ex → Fac → Ex
  emb : Fac → Ex

data Fac where
  par : Ex → Fac
  var : Fac

KG : NT → TheoryTy ℓ-zero tt
KG nE _ = Ex
KG nT _ = Fac

algG : (x : NT) → ⟦ G x ⟧TheoryTy KG ⊢ KG x
algG nE = ⊕ᴰ-elim λ where
    false → λ m z → add (z .snd .snd zero .lower)
                        (z .snd .snd (suc zero) .snd .snd (suc zero) .lower)
    true  → λ m z → emb (z .lower)
algG nT = ⊕ᴰ-elim λ where
    false → λ m z → par (z .snd .snd (suc zero) .snd .snd zero .lower)
    true  → λ m z → var

readG : (x : NT) → μ G x ⊢ KG x
readG = rec G algG
