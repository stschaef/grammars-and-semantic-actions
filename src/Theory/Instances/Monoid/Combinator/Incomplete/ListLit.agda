{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The list-literal `Maybe`-parser.  The grammar itself is
   `Combinator/Grammars/ListLit`, written once for every answer; this module
   only picks `MaybeAnswer` and runs the tests.

   Sound but not complete: `nothing` is a refusal, not a refutation. -}
open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.Combinator.Incomplete.ListLit where

open import Cubical.Data.List using ([] ; _∷_)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Maybe as M

open import Theory.Instances.Monoid.Grammars.ListLit using (Tok ; _≟T_ ; lb ; rb ; cm ; nm)
open import Theory.Instances.Monoid.Combinator.Incomplete.Base Tok _≟T_
  (ℓ-suc ℓ-zero)
import Theory.Instances.Monoid.Combinator.Grammars.ListLit MaybeAnswer as G

testList : Test _
testList = runP G.ℓG (pmore ∘⊢ G.listP)

ok? : String → M.Maybe Unit
ok? = observe testList (semact-Maybe (semact-pure tt))

accepts : passes
  (ok? at
    ( (lb ∷ rb ∷ [])                          ↦ M.just tt
    ∷ (lb ∷ nm ∷ rb ∷ [])                     ↦ M.just tt
    ∷ (lb ∷ nm ∷ cm ∷ nm ∷ rb ∷ [])           ↦ M.just tt
    ∷ (lb ∷ nm ∷ cm ∷ nm ∷ cm ∷ nm ∷ rb ∷ []) ↦ M.just tt
    ∷ [] ))
accepts = refl

rejects : passes
  (ok? at
    ( (lb ∷ [])                     ↦ M.nothing
    ∷ (lb ∷ cm ∷ rb ∷ [])           ↦ M.nothing
    ∷ (lb ∷ nm ∷ cm ∷ rb ∷ [])      ↦ M.nothing
    ∷ (lb ∷ nm ∷ nm ∷ rb ∷ [])      ↦ M.nothing
    ∷ (nm ∷ [])                     ↦ M.nothing
    ∷ [] ))
rejects = refl
