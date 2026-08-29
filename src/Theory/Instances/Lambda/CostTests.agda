{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The doubling table, computed rather than measured.

   `bc4d6a4` established that the monoid tokeniser is linear by timing it
   at 40/80/160/320/640 tokens and reading the column.  That table lives in
   a commit message and says nothing a typechecker can act on.

   Here the same claim is a term.  `Scope`'s checker, unchanged, is
   instantiated at `Costed DecAnswer` -- the grading transformer -- so it
   returns its own step count alongside its answer, and each row of the
   table is a `refl`.

   What this is NOT: a timing.  It counts framework steps, so it is blind
   to `applyStack`-style work hidden inside a reindexing and blind to
   conversion checking.  It is a claim about the algorithm; the doubling
   table remains the way you find out whether the claim describes the
   program. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Lambda.CostTests where

open import Cubical.Data.List using ([] ; _∷_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; isSetℕ ; discreteℕ)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Lambda.Scope ℕ isSetℕ discreteℕ

import Theory.Combinator.Answer.Decidable
  λEqns ℕ (λ _ → nm) termPresentation as D
open import Theory.Combinator.Cost λEqns ℕ (λ _ → nm) termPresentation

module CG = Costed D.DecAnswer
module CC = Check CG.costed

-- the checker, unchanged, reporting its own step count
steps : Ctx → RawTm → ℕ
steps Γ = CG.stepsOf (CC.scoped Γ)

-- ...and still answering, so the count describes a real run
open import Cubical.Data.Bool using (Bool ; true ; false)
import Cubical.Data.Sum as Sum

decides : Ctx → RawTm → Bool
decides Γ t = Sum.rec (λ _ → true) (λ _ → false) (CG.answerOf (CC.scoped Γ) t tt)

-- The ladder: `nest n` is n binders over a bound variable, so it has
-- n + 1 nodes.
nest : ℕ → RawTm
nest zero = tvar 0
nest (suc n) = tlam 0 (nest n)

-- THE TABLE.  One row per size, each a `refl`.
row0 : steps [] (nest 0) ≡ 2
row0 = refl

row1 : steps [] (nest 1) ≡ 4
row1 = refl

row2 : steps [] (nest 2) ≡ 6
row2 = refl

row4 : steps [] (nest 4) ≡ 10
row4 = refl

row8 : steps [] (nest 8) ≡ 18
row8 = refl

row16 : steps [] (nest 16) ≡ 34
row16 = refl

-- Doubling the input doubles the count, which is what the commit message
-- was for -- except this one is checked.
doubling : (steps [] (nest 16) + steps [] (nest 16)) ≡ steps [] (nest 32) + 2
doubling = refl

-- ...and the checker really ran: every rung still decides.
ran0 : decides [] (nest 0) ≡ false      -- `tvar 0` is open
ran0 = refl

ran4 : decides [] (nest 4) ≡ true       -- bound by the outermost binder
ran4 = refl

-- An application branches, so its count is the sum of its parts plus the
-- node -- the arithmetic `Ans-node` performs, visible.
app2 : steps [] (tapp (nest 1) (nest 1)) ≡ 9
app2 = refl

-- WHAT DOES NOT WORK, and it is the interesting part.
--
-- The obvious strengthenings are the two recurrences, quantified over all
-- terms rather than sampled at six sizes:
--
--   recurrence : (Γ : Ctx) (n : ℕ)
--     → steps Γ (nest (suc n)) ≡ 2 + (steps (0 ∷ Γ) (nest n) + 0)
--   branching  : (Γ : Ctx) (t u : RawTm)
--     → steps Γ (tapp t u) ≡ suc (steps Γ t + (steps Γ u + 0))
--
-- Both are TRUE and NEITHER is `refl`, for one reason.  With the subterms
-- free, `tmSize` is stuck, so `<-wellfounded` yields no `Acc` witness, so
-- `löb` does not unfold: `Later/Indexed` gives `löb-unfold` as a
-- PROPOSITIONAL equality, never a definitional one.  Concrete rows reduce
-- only because a concrete term has a concrete size.
--
-- So the grading buys a table that is CHECKED rather than TIMED, and stops
-- exactly there.  A general "this checker is linear" theorem has to reason
-- through `löb-unfold` by hand, and that -- not the cost algebra -- is the
-- real work.  Worth knowing before treating the transformer as more than
-- an instrument.
