{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The readout: a derivation folded to the substitution it justifies.

   `Elaborate` reads a de Bruijn index off a `Lookup` witness, because the
   witness is where the search already happened.  The same now holds here,
   and it did not used to.  `Judgment`'s `Match p v` is
   `Σ[ e ∈ Env p ] (inst p e ≡ v)`, so `bind` is a fold over `e` alone: it
   never looks at the scrutinee, and it cannot, because `v` is not one of
   its arguments.  The old `bind` read `v` off the model and `n` off the
   index and the derivation merely certified that it might; what it
   returned was a substitution nothing said was *correct*.  The equation
   in the derivation says exactly that -- `inst p e ≡ v` is "the pattern,
   filled with these bindings, is the value" -- so the readout is a
   projection and its correctness is definitional.

   The names still come off the pattern, and that is not a weakness: a
   name is a syntactic feature of `pvar n`, and `Env` is what carries the
   thing the pattern does *not* determine.

   The content is one level up.  `Any cs` is a sum over the clause list, so
   its derivations are exactly the clauses that fire, and `anyAction`
   returns the clause's *position* along with its bindings.  That sum is
   the only proof-relevant thing in the development, and it is the thing
   the three answers disagree about: `Dec` collapses it to a decision,
   `Maybe` to its leftmost summand, `ND` to all of them.

   `ND` reads out through `Answer/NonDet`'s `observeND`, the counterpart
   of `observe`: a nondeterministic answer is a list, so the action is
   applied under it and the boundary is crossed once per derivation rather
   than once. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Match.Bindings where

open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; length)
open import Cubical.Data.List using () renaming (map to mapL)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Match.Judgment public

open import Theory.Type.SemanticAction.Base
  VEqns NoVar noVarSort vPresentation public
import Theory.Combinator.Answer.Decidable
  VEqns NoVar noVarSort vPresentation as D
import Theory.Combinator.Answer.Incomplete
  VEqns NoVar noVarSort vPresentation as MB
import Theory.Combinator.Answer.NonDet
  VEqns NoVar noVarSort vPresentation as NDm

module CD = Check D.DecAnswer
module CM = Check MB.MaybeAnswer
module CN = Check NDm.NDAnswer

private variable ℓA ℓX : Level

-- A substitution, and a clause's answer: which clause, and what it bound.
Subst : Type ℓ-zero
Subst = List (ℕ × Val)

Result : Type ℓ-zero
Result = ℕ × Subst

-- The fold, over the filling and nothing else.  There are no impossible
-- head/pattern pairs to rule out, because there is no head: `Env` has one
-- clause per pattern and every one of them is inhabited.
bind : (p : Pat) → Env p → Subst
bind pwild _ = []
bind (pvar n) v = (n , v) ∷ []
bind ptrue _ = []
bind pfalse _ = []
bind (ppair p q) (e , f) = bind p e ++ bind q f

bindAction : (p : Pat) → SemanticAction (Match p) Subst
bindAction p v d = bind p (d .fst) , tt

-- ...and over a clause list, tagging each summand with its position.
anyAction : (cs : List Pat) → SemanticAction (Any cs) Result
anyAction [] = semact-⊥
anyAction (p ∷ ps) =
  semact-⊕ (semact-map (0 ,_) (bindAction p))
           (semact-map (λ r → suc (r .fst) , r .snd) (anyAction ps))

-- `ND`'s readout is `Answer/NonDet`'s `observeND`, the counterpart of
-- `observe`; this client no longer rolls its own.

-- The three front ends.  Same grammar, same action, three answers.
decideMatch : (cs : List Pat) → Val → Maybe Result
decideMatch cs = observe (CD.matchAny cs) (semact-dec (anyAction cs))

firstMatch : (cs : List Pat) → Val → Maybe Result
firstMatch cs = observe (CM.matchAny cs) (semact-Maybe (anyAction cs))

allMatches : (cs : List Pat) → Val → List Result
allMatches cs = NDm.observeND (CN.matchAny cs) (anyAction cs)

-- ...and the number of clauses that fire.  Two is a redundant clause list,
-- zero is a counterexample to exhaustiveness, and nothing but `ND` can say
-- either.
tally : (cs : List Pat) → Val → ℕ
tally cs v = length (allMatches cs v)

-- a single pattern, for comparison: at most one derivation, always
bindsOf : (p : Pat) → Val → Maybe Subst
bindsOf p = observe (CD.matched p) (semact-dec (bindAction p))
