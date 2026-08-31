{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The Dyck decider.  The parser itself is `Combinator/Grammars/Dyck`,
   written once for every answer; this module only picks `DecAnswer` and
   runs the tests. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Decidable.Dyck where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using ([] ; _∷_)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Maybe as M

open import Theory.Instances.Monoid.Grammars.Dyck
  using (Br ; lp ; rp ; _≟_ ; Dyck ; done ; nest ; S ; nilTree ; semactS)
open import Theory.Instances.Monoid.Combinator.Decidable.Base Br _≟_ (ℓ-suc ℓ-zero)
import Theory.Instances.Monoid.Combinator.Grammars.Dyck DecAnswer as G

decDyck : Decidable S
decDyck = G.dyck

-- Some tests running it

no-lp : ¬Ty S (lp ∷ [])
no-lp = theNo (decDyck (lp ∷ []) tt) Eq.refl

no-rp : ¬Ty S (rp ∷ [])
no-rp = theNo (decDyck (rp ∷ []) tt) Eq.refl

dyck-cover : Cover Bool (DecCover S)
dyck-cover = decisionCover decDyck

nil-not-refuted : ¬Ty S [] → Empty.⊥*
nil-not-refuted no = no nilTree

parseDyck : String → M.Maybe Dyck
parseDyck = observe decDyck (semact-dec semactS)

dyck-trees : passes
  (parseDyck at
    ( []                                 ↦ M.just done
    ∷ (lp ∷ rp ∷ [])                     ↦ M.just (nest done done)
    ∷ (lp ∷ rp ∷ lp ∷ rp ∷ [])           ↦ M.just (nest done (nest done done))
    ∷ (lp ∷ lp ∷ rp ∷ rp ∷ [])           ↦ M.just (nest (nest done done) done)
    ∷ (lp ∷ lp ∷ rp ∷ lp ∷ rp ∷ rp ∷ []) ↦
        M.just (nest (nest done (nest done done)) done)
    ∷ (lp ∷ lp ∷ lp ∷ rp ∷ rp ∷ rp ∷ []) ↦
        M.just (nest (nest (nest done done) done) done)
    ∷ [] ))
dyck-trees = refl

dyck-no-trees : passes
  (parseDyck at
    ( (lp ∷ [])                   ↦ M.nothing
    ∷ (rp ∷ [])                   ↦ M.nothing
    ∷ (lp ∷ lp ∷ rp ∷ [])         ↦ M.nothing
    ∷ (lp ∷ rp ∷ rp ∷ [])         ↦ M.nothing
    ∷ [] ))
dyck-no-trees = refl
