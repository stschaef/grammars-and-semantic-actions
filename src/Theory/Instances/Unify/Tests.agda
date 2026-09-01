{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
-- Tests are `refl`, so the typechecker runs the whole front end; the `ND`
-- count is `1` on solvable problems, `0` on unsolvable ones.
open import Cubical.Foundations.Prelude
module Theory.Instances.Unify.Tests where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing ; map-Maybe)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Sum as Sum
import Cubical.Data.Equality as Eq

open import Theory.Instances.Unify.Check

import Theory.Combinator.Answer.Decidable
  UEqns ℕ (λ n → n) uPresentation as D
import Theory.Combinator.Answer.Incomplete
  UEqns ℕ (λ n → n) uPresentation as MB
import Theory.Combinator.Answer.NonDet
  UEqns ℕ (λ n → n) uPresentation as NDm

module CM = Check MB.MaybeAnswer
module CN = Check NDm.NDAnswer

testSol : (n : ℕ) → ⊤Ty ⊢ MB.Maybe (Sol n)
testSol = CM.unify

parsesSol : (n : ℕ) → ⊤Ty ⊢ NDm.ND (Sol n)
parsesSol = CN.unify

unify : (n : ℕ) → Tm n → Tm n → Maybe (AList n)
unify = unifyTm

mayB : (n : ℕ) → Stack n → Bool
mayB n ps = Sum.rec (λ _ → true) (λ _ → false) (testSol n ps tt)

count : (n : ℕ) → Stack n → ℕ
count n ps = length (NDm.ndToList ps (parsesSol n ps tt))


private
  x y : Fin 2
  x = zero
  y = suc zero

  t u : Tm 2
  t = fork (var x) leaf
  u = fork leaf (var y)

  σ : AList 2
  σ = 0 , 2 , x , leaf , zero , leaf , Eq.refl

_ : unify 2 t u ≡ just σ
_ = refl

_ : applySteps (σ .snd .snd) t ≡ applySteps (σ .snd .snd) u
_ = refl

_ : unify 2 (var x) (var x) ≡ just (2 , 0 , Eq.refl)
_ = refl

_ : unify 2 (var x) (var y) ≡ just (1 , 1 , x , var zero , Eq.refl)
_ = refl

_ : unify 2 (var x) (fork (var x) leaf) ≡ nothing
_ = refl

_ : unify 2 leaf (fork leaf leaf) ≡ nothing
_ = refl

_ : unify 2 (fork (var x) (var y)) (fork leaf (fork leaf leaf))
    ≡ just (0 , 2 , x , leaf , zero , fork leaf leaf , Eq.refl)
_ = refl

_ : unify 2 (fork (var x) leaf) (fork leaf (fork leaf leaf)) ≡ nothing
_ = refl

_ : solve 2 ((var x , leaf) ∷ (var y , leaf) ∷ []) ≡ just σ
_ = refl

_ : solve 2 ((var x , leaf) ∷ (leaf , fork leaf leaf) ∷ []) ≡ nothing
_ = refl

_ : mayB 2 ((t , u) ∷ []) ≡ true
_ = refl

_ : mayB 2 ((leaf , fork leaf leaf) ∷ []) ≡ false
_ = refl

-- one derivation, never two: the most general unifier is unique
_ : count 2 ((t , u) ∷ []) ≡ 1
_ = refl

_ : count 2 ((var x , fork (var x) leaf) ∷ []) ≡ 0
_ = refl

_ : unify 2 (fork leaf leaf) (var y) ≡ just (1 , 1 , y , fork leaf leaf , Eq.refl)
_ = refl


-- the example's derivation: two `assign`s and a `tt`
theStack : Stack 2
theStack = (t , u) ∷ []

d : Sol 2 theStack
d = assign leaf refl (assign leaf refl tt)

_ : mgu 2 theStack d ≡ σ
_ = refl

-- `Unif (applyA σ)` on the nose: no transport, no second run
_ : Unif (applyA σ) theStack
_ = mguUnifies 2 theStack d

-- the unifier's type mentions the returned stack: a dependent guarantee
-- crossing `observe`
_ : map-Maybe (λ r → r .snd .fst) (solveV 2 theStack) ≡ just σ
_ = refl

_ : map-Maybe fst (solveV 2 theStack) ≡ just theStack
_ = refl

_ : map-Maybe fst (unifierTm 2 (var x) (var y)) ≡ just ((var x , var y) ∷ [])
_ = refl
