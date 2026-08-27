{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `Grammars/Arith` written once, run at all three answers.

   Nothing below re-states the grammar or the parser: `GDec.arith`,
   `GInc.arith` and `GND.arith` are the same `step` at three
   `AnswerFunctor`s.  The decider refutes, the `Maybe` parser declines, and
   the enumerator returns the empty list -- and on a well-formed expression
   all three agree, the enumeration having exactly one element because the
   grammar is unambiguous.

   The semantic action is `semact-pure tt`: what is being compared across
   the three answers is *whether* a string parses and *how many ways*, not
   the tree, which `Decidable/Arith` already witnesses. -}
open import Cubical.Foundations.Prelude
open import Theory.Instances.Monoid.Combinator.Grammars.ArithGrammar
  using (Tok ; nm ; pl ; lb ; rb ; _≟T_ ; Exp ; Lang)

module Theory.Instances.Monoid.Combinator.Grammars.ArithTests where

open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Maybe as M
open import Cubical.Data.Sigma using (_×_)

import Theory.Instances.Monoid.Combinator.Decidable.Base
  Tok _≟T_ (ℓ-suc ℓ-zero) as Dec
import Theory.Instances.Monoid.Combinator.Incomplete.Base
  Tok _≟T_ (ℓ-suc ℓ-zero) as Inc
import Theory.Instances.Monoid.Combinator.NonDet.Base
  Tok _≟T_ (ℓ-suc ℓ-zero) as ND

import Theory.Instances.Monoid.Combinator.Grammars.Arith
  Dec.DecAnswer Dec.DecDiv Dec.DecCommitting as GDec
import Theory.Instances.Monoid.Combinator.Grammars.Arith
  Inc.MaybeAnswer Inc.MaybeDiv Inc.MaybeCommitting as GInc
import Theory.Instances.Monoid.Combinator.Grammars.Arith
  ND.NDAnswer ND.NDDiv ND.NDCommitting as GND

-- One parser, three answers.

decArith : Dec.Decidable (Lang Exp)
decArith = GDec.arith

testArith : Inc.Test (Lang Exp)
testArith = GInc.arith

parsesArith : ND.Parses (Lang Exp)
parsesArith = GND.arith


open Dec using (_↦_ ; _at_ ; passes)

sem : Dec.SemanticAction (Lang Exp) Unit
sem = Dec.semact-pure tt

parseDec : Dec.String → M.Maybe Unit
parseDec = Dec.observe decArith (Dec.semact-dec sem)

parseInc : Dec.String → M.Maybe Unit
parseInc = Inc.observe testArith (Inc.semact-Maybe sem)

parseND : Dec.String → List Unit
parseND = ND.observe parsesArith (ND.semact-ND sem)

cases : List (Dec.String × M.Maybe Unit)
cases =
  ( (nm ∷ [])                                  ↦ M.just tt
  ∷ (nm ∷ pl ∷ nm ∷ [])                        ↦ M.just tt
  ∷ (nm ∷ pl ∷ nm ∷ pl ∷ nm ∷ [])              ↦ M.just tt
  ∷ (lb ∷ nm ∷ rb ∷ [])                        ↦ M.just tt
  ∷ (lb ∷ nm ∷ pl ∷ nm ∷ rb ∷ [])              ↦ M.just tt
  ∷ (lb ∷ nm ∷ pl ∷ nm ∷ rb ∷ pl ∷ nm ∷ [])    ↦ M.just tt
  ∷ (lb ∷ lb ∷ nm ∷ rb ∷ rb ∷ [])              ↦ M.just tt
  ∷ []                                         ↦ M.nothing
  ∷ (pl ∷ [])                                  ↦ M.nothing
  ∷ (nm ∷ pl ∷ [])                             ↦ M.nothing
  ∷ (lb ∷ nm ∷ [])                             ↦ M.nothing
  ∷ (lb ∷ nm ∷ rb ∷ rb ∷ [])                   ↦ M.nothing
  ∷ (nm ∷ nm ∷ [])                             ↦ M.nothing
  ∷ (lb ∷ rb ∷ [])                             ↦ M.nothing
  ∷ [] )

-- ...and the same list at `ND`, where a `just` becomes a one-element
-- enumeration: the grammar is unambiguous, so no string has two parses.
casesND : List (Dec.String × List Unit)
casesND =
  ( (nm ∷ [])                                  ↦ (tt ∷ [])
  ∷ (nm ∷ pl ∷ nm ∷ [])                        ↦ (tt ∷ [])
  ∷ (nm ∷ pl ∷ nm ∷ pl ∷ nm ∷ [])              ↦ (tt ∷ [])
  ∷ (lb ∷ nm ∷ rb ∷ [])                        ↦ (tt ∷ [])
  ∷ (lb ∷ nm ∷ pl ∷ nm ∷ rb ∷ [])              ↦ (tt ∷ [])
  ∷ (lb ∷ nm ∷ pl ∷ nm ∷ rb ∷ pl ∷ nm ∷ [])    ↦ (tt ∷ [])
  ∷ (lb ∷ lb ∷ nm ∷ rb ∷ rb ∷ [])              ↦ (tt ∷ [])
  ∷ []                                         ↦ []
  ∷ (pl ∷ [])                                  ↦ []
  ∷ (nm ∷ pl ∷ [])                             ↦ []
  ∷ (lb ∷ nm ∷ [])                             ↦ []
  ∷ (lb ∷ nm ∷ rb ∷ rb ∷ [])                   ↦ []
  ∷ (nm ∷ nm ∷ [])                             ↦ []
  ∷ (lb ∷ rb ∷ [])                             ↦ []
  ∷ [] )

dec-arith : passes (parseDec at cases)
dec-arith = refl

inc-arith : passes (parseInc at cases)
inc-arith = refl

nd-arith : passes (parseND at casesND)
nd-arith = refl
