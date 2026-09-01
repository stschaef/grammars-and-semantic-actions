{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- Free model: a stack of unification problems.  `var`/`leaf`/`fork` are
-- deliberately NOT in the signature: congruence is the machine's first
-- move, and belongs in the transition, not the alphabet.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Cubical.Data.Equality as Eq
module Theory.Instances.Unify.Base where

open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Nat using (ℕ ; isSetℕ)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)

open import Theory.Instances.Unify.Term public

UOp : Type ℓ-zero
UOp = Σ[ n ∈ ℕ ] Prob n

USig : SortedSig ℕ ℓ-zero
USig .ops = UOp
USig .arity _ = 1
USig .sortOf o _ = o .fst
USig .resultSort o = o .fst

UEqns : SortedEqns USig ℓ-zero
UEqns .eqns = ⊥
UEqns .eqnSort ()
UEqns .varCount ()
UEqns .varSort ()
UEqns .lhs ()
UEqns .rhs ()

open import Theory.Free.Base UEqns ℕ (λ n → n)

private
  uOps : Ops {σ = USig} Stack
  uOps (n , p) xs = p ∷ xs zero

  uSat : (e : UEqns .eqns)
    (ρ : (w : vars UEqns e) → Stack (UEqns .varSort e w))
    → TmRec Stack uOps ρ (UEqns .lhs e) ≡ TmRec Stack uOps ρ (UEqns .rhs e)
  uSat () ρ

  UModel : MOD UEqns ℓ-zero .ob
  UModel = (λ n → Stack n , isSetStack) , uOps , uSat

-- a stack is a list: the fold is the list recursor, the generator its nil
module Fold {ℓX} {X : ℕ → Type ℓX}
  (α : Ops {σ = USig} X) (ρ : (n : ℕ) → X n) where

  fold : (n : ℕ) → Stack n → X n
  fold n [] = ρ n
  fold n (p ∷ ps) = α (n , p) (λ _ → fold n ps)

  foldOp : (o : UOp) (ms : (a : Fin 1) → Stack (o .fst))
    → fold (o .fst) (uOps o ms) ≡ α o (λ a → fold (o .fst) (ms a))
  foldOp (n , p) ms = cong (α (n , p)) (funExt λ where zero → refl)

  module _ (f : (n : ℕ) → Stack n → X n)
    (homf : (o : UOp) (ms : (a : Fin 1) → Stack (o .fst))
          → f (o .fst) (uOps o ms) ≡ α o (λ a → f (o .fst) (ms a)))
    (fβ : (n : ℕ) → f n [] ≡ ρ n) where

    foldUniq : (n : ℕ) (ps : Stack n) → f n ps ≡ fold n ps
    foldUniq n [] = fβ n
    foldUniq n (p ∷ ps) =
        homf (n , p) (λ _ → ps)
      ∙ cong (α (n , p)) (funExt λ where zero → foldUniq n ps)

uPresentation : FreePresentation ℓ-zero
uPresentation .P = UModel
uPresentation .satStrict () ρ
uPresentation .gen n = []
uPresentation .rec isSetX α sat ρ {n} = Fold.fold α ρ n
uPresentation .recGen isSetX α sat ρ v = refl
uPresentation .recOp isSetX α sat ρ = Fold.foldOp α ρ
uPresentation .recUniq isSetX α sat ρ f homf fβ {n} =
  Fold.foldUniq α ρ f homf fβ n
