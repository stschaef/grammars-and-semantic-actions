{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- The theory whose free model is a clause matrix.

   One sort per WIDTH -- `S` is `ℕ`, and a model element at sort `n` is a
   list of `n`-column rows.  One operation per row, `consOp n r`, unary,
   taking a matrix at `n` to a matrix at `n`; one generator per width, the
   empty matrix.  So the free model at sort `n` is exactly `Mat n`, and the
   operation is indexed by external data in the same way `Unify`'s
   `consOp n p` is indexed by an equation.

   Why the matrix and not the pattern.  `Match` put the pattern in the
   index and let the guard descend on the scrutinee; there the recursion
   was structural in one argument and the theory carried the other.  Here
   NOTHING is structural: specialisation rewrites every row of the matrix
   at once, and the width goes UP at a pair.  So the choice is made by
   which side the guard can measure, and that is the matrix -- the width is
   a tiebreak and not a measure, since it grows.  The matrix is therefore
   the model and the width the index, which is also the only split under
   which `spec` and `dflt` are maps of MODEL elements and so within reach
   of `Ans-re`.

   What the signature deliberately does NOT contain: `spec`, `dflt`, and
   the head-column test.  Those are the transition function of a machine,
   and the first move of a machine belongs in the transition rather than in
   the alphabet -- the same argument `Unify/Base` makes about congruence.
   All the signature owes is the one position the recursion could descend
   to structurally, and this client never uses even that. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Cubical.Data.Equality as Eq
module Theory.Instances.PatComp.Base where

open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Nat using (ℕ ; isSetℕ)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)

open import Theory.Instances.PatComp.Matrix public

-- The signature.
MOp : Type ℓ-zero
MOp = Σ[ n ∈ ℕ ] Row n

isSetMOp : isSet MOp
isSetMOp = isSetΣ isSetℕ λ _ → isSetRow

MSig : SortedSig ℕ ℓ-zero
MSig .ops = MOp
MSig .arity _ = 1
MSig .sortOf o _ = o .fst
MSig .resultSort o = o .fst

MEqns : SortedEqns MSig ℓ-zero
MEqns .eqns = ⊥
MEqns .eqnSort ()
MEqns .varCount ()
MEqns .varSort ()
MEqns .lhs ()
MEqns .rhs ()

open import Theory.Free.Base MEqns ℕ (λ n → n)

private
  mOps : Ops {σ = MSig} Mat
  mOps (n , r) P = r ∷ P zero

  mSat : (e : MEqns .eqns)
    (ρ : (w : vars MEqns e) → Mat (MEqns .varSort e w))
    → TmRec Mat mOps ρ (MEqns .lhs e) ≡ TmRec Mat mOps ρ (MEqns .rhs e)
  mSat () ρ

  MModel : MOD MEqns ℓ-zero .ob
  MModel = (λ n → Mat n , isSetMat) , mOps , mSat

-- The fold, and its uniqueness: a matrix is a list, so both are the list
-- recursor with the generator standing for the nil.
module Fold {ℓX} {X : ℕ → Type ℓX}
  (α : Ops {σ = MSig} X) (ρ : (n : ℕ) → X n) where

  fold : (n : ℕ) → Mat n → X n
  fold n [] = ρ n
  fold n (r ∷ P) = α (n , r) (λ _ → fold n P)

  foldOp : (o : MOp) (ms : (a : Fin 1) → Mat (o .fst))
    → fold (o .fst) (mOps o ms) ≡ α o (λ a → fold (o .fst) (ms a))
  foldOp (n , r) ms = cong (α (n , r)) (funExt λ where zero → refl)

  module _ (f : (n : ℕ) → Mat n → X n)
    (homf : (o : MOp) (ms : (a : Fin 1) → Mat (o .fst))
          → f (o .fst) (mOps o ms) ≡ α o (λ a → f (o .fst) (ms a)))
    (fβ : (n : ℕ) → f n [] ≡ ρ n) where

    foldUniq : (n : ℕ) (P : Mat n) → f n P ≡ fold n P
    foldUniq n [] = fβ n
    foldUniq n (r ∷ P) =
        homf (n , r) (λ _ → P)
      ∙ cong (α (n , r)) (funExt λ where zero → foldUniq n P)

mPresentation : FreePresentation ℓ-zero
mPresentation .P = MModel
mPresentation .satStrict () ρ
mPresentation .gen n = []
mPresentation .rec isSetX α sat ρ {n} = Fold.fold α ρ n
mPresentation .recGen isSetX α sat ρ v = refl
mPresentation .recOp isSetX α sat ρ = Fold.foldOp α ρ
mPresentation .recUniq isSetX α sat ρ f homf fβ {n} =
  Fold.foldUniq α ρ f homf fβ n
