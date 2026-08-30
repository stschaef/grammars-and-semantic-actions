{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `Grammars/Arith` at `Dec`, and the decisions it computes.

   The grammar, the route and the parser are all in `Grammars/`; this file
   only picks the answer.  `Decidable/ArithTests` runs it,
   `Decidable/ArithStress` runs it at size, and `Grammars/ArithTests` runs
   the same parser at `Maybe` and at `ND`. -}
open import Cubical.Foundations.Prelude
open import Theory.Instances.Monoid.Combinator.Grammars.ArithGrammar
  using (Tok ; _≟T_ ; NT ; Exp ; Lang)

module Theory.Instances.Monoid.Combinator.Decidable.Arith where

import Theory.Instances.Monoid.Combinator.Decidable.Base
  Tok _≟T_ (ℓ-suc ℓ-zero) as Dec
open Dec using (Decidable ; ¬Ty ; theYes ; theNo) public

import Theory.Instances.Monoid.Combinator.Grammars.Arith
  Dec.DecAnswer Dec.DecDiv Dec.DecCommitting as G

decide : (N : NT) → Decidable (Lang N)
decide = G.answer

parse : Decidable (Lang Exp)
parse = decide Exp

E : _
E = Lang Exp
