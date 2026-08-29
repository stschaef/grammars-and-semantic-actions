{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- The theory whose free model is a stack of unification problems.

   One sort per scope -- `S` is `ℕ`, and a model element at sort `n` is a
   list of equations between terms over `n` unknowns.  One operation per
   equation, `consOp n p`, unary, taking a stack at `n` to a stack at `n`;
   one generator per scope, the empty stack.  So the free model at sort `n`
   is exactly `Stack n`, and the operations are indexed by external data in
   the same way `Annotated`'s `appOp B` is indexed by a type.

   The signature is thin on purpose.  A term's own structure -- `var`,
   `leaf`, `fork` -- is *not* in it, and it should not be: congruence is
   the algorithm's first move, and the first move of a machine belongs in
   the transition, not in the alphabet.  What the signature has to provide
   is the one thing the framework's node rule can use, namely the position
   the recursion descends to when the head equation turns out to be
   trivial. -}
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

-- The signature.
UOp : Type ℓ-zero
UOp = Σ[ n ∈ ℕ ] Prob n

isSetUOp : isSet UOp
isSetUOp = isSetΣ isSetℕ λ _ → isSetProb

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

-- The fold, and its uniqueness: a stack is a list, so both are the list
-- recursor with the generator standing for the nil.
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
