{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The Dyck language, run at two answers.  `Decidable/Dyck` decides, so a
   rejected word comes with a refutation; `Incomplete/Dyck` only declines,
   so the same word comes back `nothing` and nothing is proved.  On the
   words that parse, the two agree on the tree. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Combinator.Decidable.DyckTests where

open import Cubical.Data.List using ([] ; _∷_)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Maybe as M

open import Theory.Instances.Monoid.Grammars.Dyck
  using (lp ; rp ; done ; nest ; S ; nilTree)
open import Theory.Instances.Monoid.Combinator.Decidable.Dyck
import Theory.Instances.Monoid.Combinator.Incomplete.Dyck as Inc

-- The decider.  A `no` is a refutation, not an absence.

no-lp : ¬Ty S (lp ∷ [])
no-lp = theNo (decDyck (lp ∷ []) tt) Eq.refl

no-rp : ¬Ty S (rp ∷ [])
no-rp = theNo (decDyck (rp ∷ []) tt) Eq.refl

nil-not-refuted : ¬Ty S [] → Empty.⊥*
nil-not-refuted no = no nilTree

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


-- The `Maybe` parser, on the same words.  Same trees, but `nothing` is a
-- refusal: there is no `¬Ty` to be had from it.

inc-dyck-trees : passes
  (Inc.parseDyck at
    ( []                                 ↦ M.just done
    ∷ (lp ∷ rp ∷ [])                     ↦ M.just (nest done done)
    ∷ (lp ∷ rp ∷ lp ∷ rp ∷ [])           ↦ M.just (nest done (nest done done))
    ∷ (lp ∷ lp ∷ rp ∷ rp ∷ [])           ↦ M.just (nest (nest done done) done)
    ∷ (lp ∷ lp ∷ rp ∷ lp ∷ rp ∷ rp ∷ []) ↦
        M.just (nest (nest done (nest done done)) done)
    ∷ (lp ∷ lp ∷ lp ∷ rp ∷ rp ∷ rp ∷ []) ↦
        M.just (nest (nest (nest done done) done) done)
    ∷ [] ))
inc-dyck-trees = refl

inc-dyck-no-trees : passes
  (Inc.parseDyck at
    ( (lp ∷ [])                   ↦ M.nothing
    ∷ (rp ∷ [])                   ↦ M.nothing
    ∷ (lp ∷ lp ∷ rp ∷ [])         ↦ M.nothing
    ∷ (lp ∷ rp ∷ rp ∷ [])         ↦ M.nothing
    ∷ [] ))
inc-dyck-no-trees = refl
