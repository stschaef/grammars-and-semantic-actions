{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The Dyck `Maybe`-parser.  The parser itself is
   `Combinator/Grammars/Dyck`, written once for every answer; this module
   only picks `MaybeAnswer`.  The suites are in `Decidable/DyckTests`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Incomplete.Dyck where

open import Cubical.Data.Sigma using (_,_)
import Cubical.Data.Maybe as M

open import Theory.Instances.Monoid.Grammars.Dyck
  using (Br ; _≟_ ; Dyck ; S ; semactS)
open import Theory.Instances.Monoid.Combinator.Incomplete.Base
  Br _≟_ (ℓ-suc ℓ-zero)
import Theory.Instances.Monoid.Combinator.Grammars.Dyck
  MaybeAnswer as G

-- Sound but not complete: `nothing` is a refusal, not a refutation
testDyck : Test S
testDyck = G.dyck

parseDyck : String → M.Maybe Dyck
parseDyck = observe testDyck (semact-Maybe semactS)
