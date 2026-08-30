{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `Grammars/Arith` at `Dec`, at size.  These cases exist to measure how
   long the decider takes to typecheck, not to say anything the small
   cases in `Decidable/ArithTests` do not already say.  The size numerals
   below -- the `8`s and `32`s -- are the knob: raise them to make the
   measurement bigger, lower them to make the file cheap again. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Combinator.Decidable.ArithStress where

open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Combinator.Grammars.ArithGrammar
  using (Tok ; nm ; pl ; lb ; rb)
open import Theory.Instances.Monoid.Combinator.Decidable.Arith

-- `chain k` is `n + n + … + n` with k additions; `nest d` is
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
