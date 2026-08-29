{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- One unifier, three answers.  The tests are `refl`, so the typechecker
   runs the whole front end: the guarded fixpoint, the cover, the occurs
   check and the readout.

   The examples are the source's, transcribed: unify `⟨x, leaf⟩` with
   `⟨leaf, y⟩`, a variable with itself, the occurs-check failure and the
   leaf-versus-fork clash.

   `mguAction` is where a derivation becomes an answer, and it is now a
   projection: the flexible rule records the term `check` returned, so the
   derivation *is* the triangular substitution and `mgu` reads it off, the
   way `Elaborate` reads a de Bruijn index off a `Lookup`.  Every expected
   value below is unchanged by that -- the machine was always computing
   these chains; it was computing them twice.

   `Sol` is still a proposition, and the `ND` count is the observable form
   of it: `1` on every solvable problem and `0` on every unsolvable one.
   Carrying the assignment did not make the judgment ambiguous, because the
   assignment is determined -- exactly `Annotated`'s reason.

   `solveV` is the same run with `Correct`'s proof attached, so its `just`
   branch is a substitution together with the fact that it unifies.  Its
   substitution is `solve`'s, on the nose. -}
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

-- the same grammar, read three ways
testSol : (n : ℕ) → ⊤Ty ⊢ MB.Maybe (Sol n)
testSol = CM.unify

parsesSol : (n : ℕ) → ⊤Ty ⊢ NDm.ND (Sol n)
parsesSol = CN.unify

-- The front end comes from `Check`; a test only calls it.
unify : (n : ℕ) → Tm n → Tm n → Maybe (AList n)
unify = unifyTm

mayB : (n : ℕ) → Stack n → Bool
mayB n ps = Sum.rec (λ _ → true) (λ _ → false) (testSol n ps tt)

count : (n : ℕ) → Stack n → ℕ
count n ps = length (NDm.ndToList ps (parsesSol n ps tt))


-- A scope of two unknowns, and the source's example problem.
private
  x y : Fin 2
  x = zero
  y = suc zero

  t u : Tm 2
  t = fork (var x) leaf
  u = fork leaf (var y)

  -- both unknowns become `leaf`, and the scope drops to nothing
  σ : AList 2
  σ = 0 , 2 , x , leaf , zero , leaf , Eq.refl

_ : unify 2 t u ≡ just σ
_ = refl

-- ...and it really is a unifier
_ : applySteps (σ .snd .snd) t ≡ applySteps (σ .snd .snd) u
_ = refl

-- a variable unifies with itself, and needs no substitution at all
_ : unify 2 (var x) (var x) ≡ just (2 , 0 , Eq.refl)
_ = refl

-- ...whereas two distinct variables need one step
_ : unify 2 (var x) (var y) ≡ just (1 , 1 , x , var zero , Eq.refl)
_ = refl

-- a term cannot unify with a pair containing itself
_ : unify 2 (var x) (fork (var x) leaf) ≡ nothing
_ = refl

-- leaf is not a fork
_ : unify 2 leaf (fork leaf leaf) ≡ nothing
_ = refl

-- congruence descends both sides at once: two unknowns, two steps
_ : unify 2 (fork (var x) (var y)) (fork leaf (fork leaf leaf))
    ≡ just (0 , 2 , x , leaf , zero , fork leaf leaf , Eq.refl)
_ = refl

-- a clash *under* a congruence is still a clash
_ : unify 2 (fork (var x) leaf) (fork leaf (fork leaf leaf)) ≡ nothing
_ = refl

-- the same problem left as a stack of two equations, which is the shape
-- the judgment is really about
_ : solve 2 ((var x , leaf) ∷ (var y , leaf) ∷ []) ≡ just σ
_ = refl

-- an unsatisfiable stack whose *first* equation is fine
_ : solve 2 ((var x , leaf) ∷ (leaf , fork leaf leaf) ∷ []) ≡ nothing
_ = refl

-- the two incomplete answers agree with the decision
_ : mayB 2 ((t , u) ∷ []) ≡ true
_ = refl

_ : mayB 2 ((leaf , fork leaf leaf) ∷ []) ≡ false
_ = refl

-- one derivation, never two: the most general unifier is unique
_ : count 2 ((t , u) ∷ []) ≡ 1
_ = refl

_ : count 2 ((var x , fork (var x) leaf) ∷ []) ≡ 0
_ = refl

-- orientation: a rigid term against a variable is the same equation
_ : unify 2 (fork leaf leaf) (var y) ≡ just (1 , 1 , y , fork leaf leaf , Eq.refl)
_ = refl


-- THE DERIVATION, WRITTEN OUT.  This is the whole point of the refinement:
-- a derivation of the source's example is two `assign`s and a `tt`, and the
-- two terms it assigns are the two the substitution consists of.  Nothing
-- else is in it -- the `refl`s are `check`'s answers being identified with
-- them, and `tt` is the empty stack.
theStack : Stack 2
theStack = (t , u) ∷ []

d : Sol 2 theStack
d = assign leaf refl (assign leaf refl tt)

-- ...so the readout is a projection, and this is that fact.
_ : mgu 2 theStack d ≡ σ
_ = refl

-- ...and the derivation comes with the proof that its substitution
-- unifies.  The type is `Unif (applyA σ)` on the nose: no transport, no
-- second run, and the checker's answer is what supplies `d`.
_ : Unif (applyA σ) theStack
_ = mguUnifies 2 theStack d

-- The verified front end returns the stack it was asked about paired with a
-- unifier *of that stack* -- the second component's type mentions the first,
-- which is what a dependent guarantee has to do to cross `observe`.
_ : map-Maybe (λ r → r .snd .fst) (solveV 2 theStack) ≡ just σ
_ = refl

_ : map-Maybe fst (solveV 2 theStack) ≡ just theStack
_ = refl

_ : map-Maybe fst (unifierTm 2 (var x) (var y)) ≡ just ((var x , var y) ∷ [])
_ = refl
