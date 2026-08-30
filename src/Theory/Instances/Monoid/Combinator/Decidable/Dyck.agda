{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The Dyck decider.  The parser itself is `Combinator/Grammars/Dyck`,
   written once for every answer; this module only picks `DecAnswer`.
   The suites are in `Decidable/DyckTests`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Decidable.Dyck where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Sigma using (_,_)
import Cubical.Data.Maybe as M

open import Theory.Instances.Monoid.Grammars.Dyck
  using (Br ; _≟_ ; Dyck ; S ; semactS)
open import Theory.Instances.Monoid.Combinator.Decidable.Base
  Br _≟_ (ℓ-suc ℓ-zero) public
import Theory.Instances.Monoid.Combinator.Grammars.Dyck DecAnswer as G

decDyck : Decidable S
decDyck = G.dyck

dyck-cover : Cover Bool (DecCover S)
dyck-cover = decisionCover decDyck

parseDyck : String → M.Maybe Dyck
parseDyck = observe decDyck (semact-dec semactS)
