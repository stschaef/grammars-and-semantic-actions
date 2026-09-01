{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Readout: fold the derivation to the substitution it justifies.  `bind`
   folds the `Env` alone (`v` is not an argument); the derivation's
   equation makes the readout's correctness definitional. -}
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

-- `Result`: which clause fired, and what it bound.
Subst : Type ℓ-zero
Subst = List (ℕ × Val)

Result : Type ℓ-zero
Result = ℕ × Subst

-- No impossible cases: `Env` has one inhabited clause per pattern.
bind : (p : Pat) → Env p → Subst
bind pwild _ = []
bind (pvar n) v = (n , v) ∷ []
bind ptrue _ = []
bind pfalse _ = []
bind (ppair p q) (e , f) = bind p e ++ bind q f

bindAction : (p : Pat) → SemanticAction (Match p) Subst
bindAction p v d = bind p (d .fst) , tt

anyAction : (cs : List Pat) → SemanticAction (Any cs) Result
anyAction [] = semact-⊥
anyAction (p ∷ ps) =
  semact-⊕ (semact-map (0 ,_) (bindAction p))
           (semact-map (λ r → suc (r .fst) , r .snd) (anyAction ps))

decideMatch : (cs : List Pat) → Val → Maybe Result
decideMatch cs = observe (CD.matchAny cs) (semact-dec (anyAction cs))

firstMatch : (cs : List Pat) → Val → Maybe Result
firstMatch cs = observe (CM.matchAny cs) (semact-Maybe (anyAction cs))

allMatches : (cs : List Pat) → Val → List Result
allMatches cs = NDm.observeND (CN.matchAny cs) (anyAction cs)

-- 2+ = redundant clause list, 0 = inexhaustive; only `ND` can say either.
tally : (cs : List Pat) → Val → ℕ
tally cs v = length (allMatches cs v)

bindsOf : (p : Pat) → Val → Maybe Subst
bindsOf p = observe (CD.matched p) (semact-dec (bindAction p))
