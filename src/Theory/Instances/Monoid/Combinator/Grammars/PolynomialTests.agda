{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `Grammars/Polynomial` written once, run at all three answers.

   Variables are `Bool`, so `x` and `y`; numerals are `ℕ`.  The decider
   refutes, the `Maybe` parser declines and the enumerator returns the
   empty list, and on a well-formed polynomial all three agree -- the
   enumeration having exactly one element, since the grammar is
   left-factored and hence unambiguous. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Combinator.Grammars.PolynomialTests where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Maybe as M

_≟B_ : (a b : Bool) → (a Eq.≡ b) Sum.⊎ ((a Eq.≡ b) → Empty.⊥)
true ≟B true = Sum.inl Eq.refl
false ≟B false = Sum.inl Eq.refl
true ≟B false = Sum.inr λ ()
false ≟B true = Sum.inr λ ()

import Theory.Instances.Monoid.Combinator.Grammars.PolyGrammar
  Bool _≟B_ as PG
open PG using (Tok ; lp ; rp ; plus ; times ; slash ; minus ; caret
              ; var ; nat ; expr ; Expr)

import Theory.Instances.Monoid.Combinator.Decidable.Base
  Tok PG._≟_ (ℓ-suc ℓ-zero) as Dec
import Theory.Instances.Monoid.Combinator.Incomplete.Base
  Tok PG._≟_ (ℓ-suc ℓ-zero) as Inc
import Theory.Instances.Monoid.Combinator.NonDet.Base
  Tok PG._≟_ (ℓ-suc ℓ-zero) as ND

import Theory.Instances.Monoid.Combinator.Grammars.Polynomial
  Bool _≟B_ Dec.DecAnswer Dec.DecDiv Dec.DecCommitting as GDec
import Theory.Instances.Monoid.Combinator.Grammars.Polynomial
  Bool _≟B_ Inc.MaybeAnswer Inc.MaybeDiv Inc.MaybeCommitting as GInc
import Theory.Instances.Monoid.Combinator.Grammars.Polynomial
  Bool _≟B_ ND.NDAnswer ND.NDDiv ND.NDCommitting as GND

-- One parser, three answers.

decPoly : Dec.Decidable Expr
decPoly = GDec.poly

testPoly : Inc.Test Expr
testPoly = GInc.poly

parsesPoly : ND.Parses Expr
parsesPoly = GND.poly


open Dec using (_↦_ ; _at_ ; passes)

sem : Dec.SemanticAction Expr Unit
sem = Dec.semact-pure tt

parseDec : Dec.String → M.Maybe Unit
parseDec = Dec.observe decPoly (Dec.semact-dec sem)

parseInc : Dec.String → M.Maybe Unit
parseInc = Inc.observe testPoly (Inc.semact-Maybe sem)

parseND : Dec.String → List Unit
parseND = ND.observe parsesPoly (ND.semact-ND sem)

x y : Tok
x = var true
y = var false

-- accepted: `x`, `3`, `3/4`, `x + y`, `(x)`, `x^2`, `-x`, `x * (y + 1)`
-- rejected: empty, a bare operator, a trailing operator, an unclosed
-- bracket, `/` with no denominator, juxtaposition, `()`
cases : List (Dec.String × M.Maybe Unit)
cases =
  ( (x ∷ [])                                        ↦ M.just tt
  ∷ (nat 3 ∷ [])                                    ↦ M.just tt
  ∷ (nat 3 ∷ slash ∷ nat 4 ∷ [])                    ↦ M.just tt
  ∷ (x ∷ plus ∷ y ∷ [])                             ↦ M.just tt
  ∷ (lp ∷ x ∷ rp ∷ [])                              ↦ M.just tt
  ∷ (x ∷ caret ∷ nat 2 ∷ [])                        ↦ M.just tt
  ∷ (minus ∷ x ∷ [])                                ↦ M.just tt
  ∷ (x ∷ times ∷ lp ∷ y ∷ plus ∷ nat 1 ∷ rp ∷ [])   ↦ M.just tt
  ∷ []                                              ↦ M.nothing
  ∷ (plus ∷ [])                                     ↦ M.nothing
  ∷ (x ∷ plus ∷ [])                                 ↦ M.nothing
  ∷ (lp ∷ x ∷ [])                                   ↦ M.nothing
  ∷ (nat 3 ∷ slash ∷ [])                            ↦ M.nothing
  ∷ (x ∷ y ∷ [])                                    ↦ M.nothing
  ∷ (lp ∷ rp ∷ [])                                  ↦ M.nothing
  ∷ [] )

casesND : List (Dec.String × List Unit)
casesND =
  ( (x ∷ [])                                        ↦ (tt ∷ [])
  ∷ (nat 3 ∷ [])                                    ↦ (tt ∷ [])
  ∷ (nat 3 ∷ slash ∷ nat 4 ∷ [])                    ↦ (tt ∷ [])
  ∷ (x ∷ plus ∷ y ∷ [])                             ↦ (tt ∷ [])
  ∷ (lp ∷ x ∷ rp ∷ [])                              ↦ (tt ∷ [])
  ∷ (x ∷ caret ∷ nat 2 ∷ [])                        ↦ (tt ∷ [])
  ∷ (minus ∷ x ∷ [])                                ↦ (tt ∷ [])
  ∷ (x ∷ times ∷ lp ∷ y ∷ plus ∷ nat 1 ∷ rp ∷ [])   ↦ (tt ∷ [])
  ∷ []                                              ↦ []
  ∷ (plus ∷ [])                                     ↦ []
  ∷ (x ∷ plus ∷ [])                                 ↦ []
  ∷ (lp ∷ x ∷ [])                                   ↦ []
  ∷ (nat 3 ∷ slash ∷ [])                            ↦ []
  ∷ (x ∷ y ∷ [])                                    ↦ []
  ∷ (lp ∷ rp ∷ [])                                  ↦ []
  ∷ [] )

dec-poly : passes (parseDec at cases)
dec-poly = refl

inc-poly : passes (parseInc at cases)
inc-poly = refl

nd-poly : passes (parseND at casesND)
nd-poly = refl
