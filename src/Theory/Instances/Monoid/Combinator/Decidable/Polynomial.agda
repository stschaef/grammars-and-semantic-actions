{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `Grammars/Polynomial` at `Dec`.

   The grammar is `Grammars/PolyGrammar`, the parser is
   `Grammars/Polynomial`, and both are answer-free; this file picks the
   answer.  `Grammars/PolynomialTests` runs the same parser at `Maybe` and
   at `ND` as well. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Combinator.Decidable.Polynomial
  (V : Type ℓ-zero)
  (_≟V_ : (a b : V) → (a Eq.≡ b) Sum.⊎ ((a Eq.≡ b) → Empty.⊥))
  where

open import Theory.Instances.Monoid.Combinator.Grammars.PolyGrammar
  V _≟V_ public

import Theory.Instances.Monoid.Combinator.Decidable.Base
  Tok _≟_ (ℓ-suc ℓ-zero) as Dec

import Theory.Instances.Monoid.Combinator.Grammars.Polynomial
  V _≟V_ Dec.DecAnswer Dec.DecDiv Dec.DecCommitting as G

decideExpr : Dec.Decidable Expr
decideExpr = G.answer expr

decideRest : Dec.Decidable Rest
decideRest = G.answer rest

decideNumTail : Dec.Decidable NumTail
decideNumTail = G.answer numTail
