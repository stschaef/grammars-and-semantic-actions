{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The cover `Infer/Typing`'s header says does not exist.

   That header's closing paragraph states the structural fact it had:

     a judgment refuted NODE BY NODE gets completeness from the cover's
     `total`, free; a judgment whose refutation is an existential over
     SUBSTITUTIONS gets nothing, because no cover of the term model splits
     by solvability.

   The first half stands.  The second is false, and this module is the
   counterexample: `solvabilityCover n` is a cover of `Stack n` whose two
   cells are "some substitution unifies this stack" and its refutation.

   WHY IT IS NOT CIRCULAR, which is the only interesting question.  The
   cover is built from a decision, but not from a decision for its own
   cell.  What the framework hands over is `CD.unify n`, a decision for
   `Sol` -- "the machine runs to completion" -- and `Sol` is not
   solvability: `Correct` gets from the first to the second and says the
   converse is missing.  `Solvable`'s cover therefore costs exactly the
   missing converse, `Solvable/complete`, and its `total` is that theorem
   read out.  `dec-retract` is where the two meet, and both of its maps are
   theorems rather than definitional unfoldings -- which is precisely the
   situation `Combinator/Complete` describes, where `total` is as hard as
   completeness because it IS completeness.

   WHAT THE COVER IS NOT.  It is not a refinement of the node cover.  The
   stack theory's `stackCover` splits by the head equation and stops there;
   solvability is not a property of the head, and no amount of no-confusion
   for `Tm` produces this cover on its own.  What produces it is the
   checker's own recursion -- scope down at the flexible rule, stack down
   everywhere else -- plus the three lemmas `Correct` named.  So the honest
   summary is that a solvability cover is available, at the price of the
   algorithm's completeness proof, and is not available structurally.

   Of the three obligations `Correct` lists, two were work and one looked
   like an obstruction, and only the last is worth restating.  What
   unblocked RESTRICTION was changing the CARRIED ANSWER and nothing else:
   `Solvable` quantifies over substitutions, where restriction along
   `thin x` is composition, while `Unifier` quantifies over `AList`s, where
   it is not.  `Correct`'s `n = 1` counterexample refutes the
   representability of the restricted answer as a chain; it never refuted
   the premise's solvability, and reading it as though it did is what
   turned a page of work into a reported impossibility. -}
open import Cubical.Foundations.Prelude
module Theory.Instances.Unify.Cover where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Sum as Sum

open import Theory.Instances.Unify.Check
open import Theory.Instances.Unify.Solvable

open import Theory.Combinator.Complete UEqns ℕ (λ n → n) uPresentation
  using (asCover ; fromCover)

-- Solvability as a grammar over the stack theory: the model element is the
-- stack, and the proposition is that SOME substitution, into SOME scope,
-- unifies it.
SolvableTy : (n : ℕ) → TheoryTy ℓ-zero n
SolvableTy n = Solvable n

-- The decision, transported along the equivalence.  Neither map is free:
-- `solvableOf` is `Correct`'s theorem and `complete` is its converse.
decSolvable : (n : ℕ) → Decidable (SolvableTy n)
decSolvable n = dec-retract (solvableOf n) (complete n) (CD.unify n)

-- ...and the cover, whose `total` says every stack is either unified by
-- some substitution or unified by none, and whose `disjoint` says never
-- both.
solvabilityCover : (n : ℕ) → Cover Bool (DecCover (SolvableTy n))
solvabilityCover n = asCover (decSolvable n)

-- Read back, so that the identification is used and not merely asserted.
solvabilityDecides : (n : ℕ) → Decidable (SolvableTy n)
solvabilityDecides n = fromCover (solvabilityCover n)


-- WHAT THE COVER COMPUTES.  The tests are `refl`, so the typechecker runs
-- the checker and then reads the answer through both maps of
-- `dec-retract`.  The affirming cell now CARRIES the unifying
-- substitution, and the refuting cell is what makes the two `false`s below
-- mean "no substitution unifies this" rather than "the machine stopped" --
-- which is the entire difference this module is about.
private
  x y : Fin 2
  x = zero
  y = suc zero

  solved : Stack 2
  solved = (fork (var x) leaf , fork leaf (var y)) ∷ []

  occurs : Stack 2
  occurs = (var x , fork (var x) leaf) ∷ []

  clash : Stack 2
  clash = (leaf , fork leaf leaf) ∷ []

  verdict : (n : ℕ) → Stack n → Bool
  verdict n ps = isYes (decSolvable n ps tt)

  -- the substitution the affirming cell holds, read one unknown at a time
  witness : (n : ℕ) → Stack n → Fin n → Maybe (Σ[ m ∈ ℕ ] Tm m)
  witness n ps v = Sum.rec (λ s → just (s .fst , s .snd .fst v))
                           (λ _ → nothing) (decSolvable n ps tt)

_ : verdict 2 solved ≡ true
_ = refl

_ : witness 2 solved x ≡ just (0 , leaf)
_ = refl

_ : witness 2 solved y ≡ just (0 , leaf)
_ = refl

_ : verdict 2 occurs ≡ false
_ = refl

_ : verdict 2 clash ≡ false
_ = refl

-- ...and the cover's own reading of the same run, so that `total` is used
-- and not merely exhibited.
_ : isYes (solvabilityDecides 2 solved tt) ≡ true
_ = refl

_ : isYes (solvabilityDecides 2 occurs tt) ≡ false
_ = refl
