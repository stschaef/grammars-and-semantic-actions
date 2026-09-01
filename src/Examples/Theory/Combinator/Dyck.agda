{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `Grammars/Dyck` written once, run at all three answers: the same `step`
   at three `AnswerFunctor`s.  On a well-bracketed word all three agree. -}
import Cubical.Data.Empty as Empty
open import Cubical.Foundations.Prelude

module Examples.Theory.Combinator.Dyck where

open import Cubical.Data.List using (List ; [] ; _∷_)
import Cubical.Data.Maybe as M

open import Theory.Instances.Monoid.Grammars.Dyck
  using (Br ; lp ; rp ; _≟_ ; Dyck ; done ; nest ; S ; semactS ; nilTree)

import Theory.Instances.Monoid.Combinator.Decidable.Base
  Br _≟_ (ℓ-suc ℓ-zero) as Dec
import Theory.Instances.Monoid.Combinator.Incomplete.Base
  Br _≟_ (ℓ-suc ℓ-zero) as Inc
import Theory.Instances.Monoid.Combinator.NonDet.Base
  Br _≟_ (ℓ-suc ℓ-zero) as ND

import Theory.Instances.Monoid.Combinator.Grammars.Dyck
  Dec.DecAnswer as GDec
import Theory.Instances.Monoid.Combinator.Grammars.Dyck
  Inc.MaybeAnswer as GInc
import Theory.Instances.Monoid.Combinator.Grammars.Dyck
  ND.NDAnswer as GND

decDyck : Dec.Decidable S
decDyck = GDec.dyck

testDyck : Inc.Test S
testDyck = GInc.dyck

parsesDyck : ND.Parses S
parsesDyck = GND.dyck


open import Theory.Type.SemanticAction.Testing using (_↦_ ; _at_ ; passes)

parseDec : Dec.String → M.Maybe Dyck
parseDec = Dec.observe decDyck (Dec.semact-dec semactS)

parseInc : Dec.String → M.Maybe Dyck
parseInc = Inc.observe testDyck (Inc.semact-Maybe semactS)

parseND : Dec.String → List Dyck
parseND = ND.observe parsesDyck (ND.semact-ND semactS)

dec-trees : passes
  (parseDec at
    ( []                       ↦ M.just done
    ∷ (lp ∷ rp ∷ [])           ↦ M.just (nest done done)
    ∷ (lp ∷ lp ∷ rp ∷ rp ∷ []) ↦ M.just (nest (nest done done) done)
    ∷ (lp ∷ [])                ↦ M.nothing
    ∷ (rp ∷ [])                ↦ M.nothing
    ∷ [] ))
dec-trees = refl

inc-trees : passes
  (parseInc at
    ( []                       ↦ M.just done
    ∷ (lp ∷ rp ∷ [])           ↦ M.just (nest done done)
    ∷ (lp ∷ lp ∷ rp ∷ rp ∷ []) ↦ M.just (nest (nest done done) done)
    ∷ (lp ∷ [])                ↦ M.nothing
    ∷ (rp ∷ [])                ↦ M.nothing
    ∷ [] ))
inc-trees = refl

-- exactly one parse each: the enumeration witnesses unambiguity
nd-trees : passes
  (parseND at
    ( []                       ↦ (done ∷ [])
    ∷ (lp ∷ rp ∷ [])           ↦ (nest done done ∷ [])
    ∷ (lp ∷ lp ∷ rp ∷ rp ∷ []) ↦ (nest (nest done done) done ∷ [])
    ∷ (lp ∷ [])                ↦ []
    ∷ (rp ∷ [])                ↦ []
    ∷ [] ))
nd-trees = refl

-- ε parses (the decision cannot refute the empty word)
nil-not-refuted : Dec.¬Ty S [] → Empty.⊥*
nil-not-refuted no = no nilTree
