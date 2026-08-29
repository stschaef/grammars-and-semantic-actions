{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- One unifier, three answers.  The tests are `refl`, so the typechecker
   runs the whole front end: the guarded fixpoint, the cover, the occurs
   check and the readout.

   The examples are the source's, transcribed: unify `⟨x, leaf⟩` with
   `⟨leaf, y⟩`, a variable with itself, the occurs-check failure and the
   leaf-versus-fork clash.

   `mguAction` is where a derivation becomes an answer.  `Sol` is a
   proposition -- the machine is deterministic, so a derivation is only the
   news that it finished -- and the substitution is recomputed by `mgu`,
   from the same `check` the derivation was built by.  That is the one
   place this development is thinner than `Elaborate`, where the derivation
   *is* the de Bruijn index; here it could be, at the cost of carrying
   `check`'s answer in the judgment, and nothing else would change.

   The `ND` count is worth reading as a statement: it is `1` on every
   solvable problem and `0` on every unsolvable one, and one is exactly the
   uniqueness of the most general unifier, made observable. -}
open import Cubical.Foundations.Prelude
module Theory.Instances.Unify.Tests where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Sum as Sum
import Cubical.Data.Equality as Eq

open import Theory.Instances.Unify.Check

open import Theory.Type.SemanticAction.Base UEqns ℕ (λ n → n) uPresentation

import Theory.Combinator.Answer.Decidable
  UEqns ℕ (λ n → n) uPresentation as D
import Theory.Combinator.Answer.Incomplete
  UEqns ℕ (λ n → n) uPresentation as MB
import Theory.Combinator.Answer.NonDet
  UEqns ℕ (λ n → n) uPresentation as NDm

module CD = Check D.DecAnswer
module CM = Check MB.MaybeAnswer
module CN = Check NDm.NDAnswer

-- the same grammar, read three ways
decideSol : (n : ℕ) → D.Decidable (Sol n)
decideSol = CD.unify

testSol : (n : ℕ) → ⊤Ty ⊢ MB.Maybe (Sol n)
testSol = CM.unify

parsesSol : (n : ℕ) → ⊤Ty ⊢ NDm.ND (Sol n)
parsesSol = CN.unify

-- ...and the readout, as a semantic action, so that the boundary between
-- the internal term and the external value is crossed once, in `observe`.
mguAction : (n : ℕ) → SemanticAction (Sol n) (AList n)
mguAction n ps d = mgu n ps d , tt

solve : (n : ℕ) → Stack n → Maybe (AList n)
solve n = observe (decideSol n) (semact-dec (mguAction n))

unify : (n : ℕ) → Tm n → Tm n → Maybe (AList n)
unify n t u = solve n ((t , u) ∷ [])

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
