{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `list ::= '[' ( n (',' n)* )? ']'`, run at two answers.
   `Decidable/ListLit` decides, so a rejection is a refutation;
   `Incomplete/ListLit` only declines.  The two grammars are the same
   `sepBy`, so the accepted and rejected words are the same words. -}
open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.Combinator.Decidable.ListLitTests where

open import Cubical.Data.List using ([] ; _∷_)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Maybe as M

open import Theory.Instances.Monoid.Combinator.Decidable.ListLit
import Theory.Instances.Monoid.Combinator.Incomplete.ListLit as Inc

-- The decider.

accepted : passes
  (ok? at
    ( (lb ∷ rb ∷ [])                          ↦ M.just tt
    ∷ (lb ∷ nm ∷ rb ∷ [])                     ↦ M.just tt
    ∷ (lb ∷ nm ∷ cm ∷ nm ∷ rb ∷ [])           ↦ M.just tt
    ∷ (lb ∷ nm ∷ cm ∷ nm ∷ cm ∷ nm ∷ rb ∷ []) ↦ M.just tt
    ∷ [] ))
accepted = refl

rejected : passes
  (ok? at
    ( (lb ∷ [])                     ↦ M.nothing
    ∷ (lb ∷ cm ∷ rb ∷ [])           ↦ M.nothing
    ∷ (lb ∷ nm ∷ cm ∷ rb ∷ [])      ↦ M.nothing
    ∷ (lb ∷ nm ∷ nm ∷ rb ∷ [])      ↦ M.nothing
    ∷ (nm ∷ [])                     ↦ M.nothing
    ∷ [] ))
rejected = refl


-- The `Maybe` parser.  Its token type is its own, so it is qualified; the
-- words and the answers are the ones above, with `nothing` now a refusal
-- rather than a refutation.

inc-accepted : passes
  (Inc.ok? at
    ( (Inc.lb ∷ Inc.rb ∷ [])                                      ↦ M.just tt
    ∷ (Inc.lb ∷ Inc.nm ∷ Inc.rb ∷ [])                             ↦ M.just tt
    ∷ (Inc.lb ∷ Inc.nm ∷ Inc.cm ∷ Inc.nm ∷ Inc.rb ∷ [])           ↦ M.just tt
    ∷ (Inc.lb ∷ Inc.nm ∷ Inc.cm ∷ Inc.nm ∷ Inc.cm ∷ Inc.nm ∷ Inc.rb ∷ [])
        ↦ M.just tt
    ∷ [] ))
inc-accepted = refl

inc-rejected : passes
  (Inc.ok? at
    ( (Inc.lb ∷ [])                               ↦ M.nothing
    ∷ (Inc.lb ∷ Inc.cm ∷ Inc.rb ∷ [])             ↦ M.nothing
    ∷ (Inc.lb ∷ Inc.nm ∷ Inc.cm ∷ Inc.rb ∷ [])    ↦ M.nothing
    ∷ (Inc.lb ∷ Inc.nm ∷ Inc.nm ∷ Inc.rb ∷ [])    ↦ M.nothing
    ∷ (Inc.nm ∷ [])                               ↦ M.nothing
    ∷ [] ))
inc-rejected = refl
