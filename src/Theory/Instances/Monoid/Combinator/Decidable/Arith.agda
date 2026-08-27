{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `Grammars/Arith` at `Dec`, and the decisions it computes.

   The grammar, the route and the parser are all in `Grammars/`; this file
   picks the answer and runs it.  `Grammars/ArithTests` runs the same parser
   at `Maybe` and at `ND`. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Equality as Eq
open import Theory.Instances.Monoid.Combinator.Grammars.ArithGrammar
  using (Tok ; nm ; pl ; lb ; rb ; _≟T_ ; NT ; Exp ; Exp' ; Lang)

module Theory.Instances.Monoid.Combinator.Decidable.Arith where

open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Unit using (tt)

import Theory.Instances.Monoid.Combinator.Decidable.Base
  Tok _≟T_ (ℓ-suc ℓ-zero) as Dec
open Dec using (Decidable ; ¬Ty ; theYes ; theNo)

import Theory.Instances.Monoid.Combinator.Grammars.Arith
  Dec.DecAnswer Dec.DecDiv Dec.DecCommitting as G

decide : (N : NT) → Decidable (Lang N)
decide = G.answer

parse : Decidable (Lang Exp)
parse = decide Exp

E : _
E = Lang Exp

yes-n : E (nm ∷ [])
yes-n = theYes (parse (nm ∷ []) tt) Eq.refl

yes-add : E (nm ∷ pl ∷ nm ∷ [])
yes-add = theYes (parse (nm ∷ pl ∷ nm ∷ []) tt) Eq.refl

yes-add3 : E (nm ∷ pl ∷ nm ∷ pl ∷ nm ∷ [])
yes-add3 = theYes (parse (nm ∷ pl ∷ nm ∷ pl ∷ nm ∷ []) tt) Eq.refl

yes-paren : E (lb ∷ nm ∷ rb ∷ [])
yes-paren = theYes (parse (lb ∷ nm ∷ rb ∷ []) tt) Eq.refl

yes-paren-add : E (lb ∷ nm ∷ pl ∷ nm ∷ rb ∷ [])
yes-paren-add = theYes (parse (lb ∷ nm ∷ pl ∷ nm ∷ rb ∷ []) tt) Eq.refl

yes-mixed : E (lb ∷ nm ∷ pl ∷ nm ∷ rb ∷ pl ∷ nm ∷ [])
yes-mixed = theYes (parse (lb ∷ nm ∷ pl ∷ nm ∷ rb ∷ pl ∷ nm ∷ []) tt) Eq.refl

yes-nest : E (lb ∷ lb ∷ nm ∷ rb ∷ rb ∷ [])
yes-nest = theYes (parse (lb ∷ lb ∷ nm ∷ rb ∷ rb ∷ []) tt) Eq.refl

-- Rejected: each `no` is a refutation, not an absence.

no-nil : ¬Ty E []
no-nil = theNo (parse [] tt) Eq.refl

no-plus : ¬Ty E (pl ∷ [])
no-plus = theNo (parse (pl ∷ []) tt) Eq.refl

no-trailing : ¬Ty E (nm ∷ pl ∷ [])
no-trailing = theNo (parse (nm ∷ pl ∷ []) tt) Eq.refl

no-unclosed : ¬Ty E (lb ∷ nm ∷ [])
no-unclosed = theNo (parse (lb ∷ nm ∷ []) tt) Eq.refl

no-extra-close : ¬Ty E (lb ∷ nm ∷ rb ∷ rb ∷ [])
no-extra-close = theNo (parse (lb ∷ nm ∷ rb ∷ rb ∷ []) tt) Eq.refl

no-juxtapose : ¬Ty E (nm ∷ nm ∷ [])
no-juxtapose = theNo (parse (nm ∷ nm ∷ []) tt) Eq.refl

no-empty-parens : ¬Ty E (lb ∷ rb ∷ [])
no-empty-parens = theNo (parse (lb ∷ rb ∷ []) tt) Eq.refl

-- Scale.  `chain k` is `n + n + … + n` with k additions; `nest d` is
-- `[[…[n]…]]` at depth d.

chain : ℕ → List Tok
chain zero = nm ∷ []
chain (suc j) = nm ∷ pl ∷ chain j

nest : ℕ → List Tok
nest zero = nm ∷ []
nest (suc e) = lb ∷ (nest e ++ (rb ∷ []))

yes-chain8 : E (chain 8)
yes-chain8 = theYes (parse (chain 8) tt) Eq.refl

yes-chain32 : E (chain 32)
yes-chain32 = theYes (parse (chain 32) tt) Eq.refl

yes-nest8 : E (nest 8)
yes-nest8 = theYes (parse (nest 8) tt) Eq.refl

yes-nest32 : E (nest 32)
yes-nest32 = theYes (parse (nest 32) tt) Eq.refl

no-nest32 : ¬Ty E (lb ∷ nest 32)
no-nest32 = theNo (parse (lb ∷ nest 32) tt) Eq.refl
