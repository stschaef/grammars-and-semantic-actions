{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- The theory whose free model is a clause matrix: one sort per width, one
   operation per row.  The width is a tiebreak, not a measure (it goes UP at
   a pair); `spec`/`dflt` are a machine's transition, not its alphabet. -}
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

MOp : Type ℓ-zero
MOp = Σ[ n ∈ ℕ ] Row n

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

-- a matrix is a list: fold and uniqueness are the list recursor, with the generator as nil
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
