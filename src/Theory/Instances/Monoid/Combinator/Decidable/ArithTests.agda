{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `Grammars/Arith` at `Dec`, on small words.  Every `Eq.refl` is the
   parser running; a `no-` case is a refutation, not an absence.  The
   same parser at size is `Decidable/ArithStress`. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Combinator.Decidable.ArithTests where

open import Cubical.Data.List using ([] ; _∷_)
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Combinator.Grammars.ArithGrammar
  using (nm ; pl ; lb ; rb)
open import Theory.Instances.Monoid.Combinator.Decidable.Arith

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
