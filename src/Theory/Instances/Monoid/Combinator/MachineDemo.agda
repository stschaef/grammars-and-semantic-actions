{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Configurations, run.  `Machine.agda` gives the types; this runs them.

   The point of the file is one comparison: the *same* parser `px`, cut
   against two different configurations, recognises two different languages.
   That is what a configuration is -- the context the parser runs in. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.MachineDemo where

open import Cubical.Data.List using ([] ; _∷_)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Unit using (tt ; tt*)

open import Theory.Instances.Monoid.Combinator.ExprGrammar
open import Theory.Instances.Monoid.Combinator.Core Tk _≟K_
import Theory.Instances.Monoid.Combinator.Incomplete.Base Tk _≟K_ ℓ-zero as Inc
import Theory.Instances.Monoid.Combinator.Machine Tk _≟K_ as Mch

open Combinators Inc.MaybeAnswer using (Parser ; tok ; pmore ; □Ans-ε)
open CovCombinators Inc.MaybeAnswer Inc.MaybeCov using (mapP)

-- the parser for a single `x`, with its tags adjusted to ⟨□⟩⟨□⟩
px : ⊤Ty ⊢ Parser ℓM ⟨□⟩ ⟨□⟩ (litSet ‵x)
px = pmore ∘⊢ tok ‵x

-- Both configurations answer to the same goal: a `Maybe` of the whole parse
-- `x +`.  `Runner` already packages `Config` at exactly that goal.
module R = Mch.Runner Inc.MaybeAnswer {ℓK = ℓ-zero} {A = litSet ‵x ⊗Set litSet ‵+}

-- CONTEXT 1: nothing follows.  `K = ε`, so a parse must END after what it
-- expects -- and what it expects is the whole of `x +`.
ctxEnd : ⊤Ty ⊢ R.Config (ℓ-max ℓM ℓ-zero) ⟨□⟩ ⟨□⟩ (litSet ‵x ⊗Set litSet ‵+)
ctxEnd = R.initial

-- CONTEXT 2: a `+` is still owed.  `push` moves `litSet ‵+` onto `K`, so
-- this context expects only an `x`, with the `+` pending behind it.
ctxPlus : ⊤Ty ⊢ R.Config _ ⟨□⟩ ⟨□⟩ (litSet ‵x)
ctxPlus = R.push (pmore ∘⊢ tok ‵+) R.initial ∘⊢ (id⊢ ,& id⊢)

-- THE COMPARISON.  The same `px`, cut against the two contexts.
runEnd : ⊤Ty ⊢ ty (Inc.MaybeSet (litSet ‵x ⊗Set litSet ‵+))
runEnd = R.cut ∘⊢ (px ,& ctxPlus)

-- ...and it runs.  `x +` is accepted by the pushed context: the `x` fills the
-- hole, the pending `+` is discharged from `K`, and the goal comes back
-- `just`.  `Eq.refl` is the whole check.
acceptsXPlus :
  runEnd (‵x ∷ ‵+ ∷ []) tt
  Eq.≡ just {A = literal ‵x ⊗ literal ‵+} (‵x ∷ ‵+ ∷ [])
         (two (‵x ∷ []) (‵+ ∷ []) , Eq.refl , (Eq.refl , (Eq.refl , tt*)))
acceptsXPlus = Eq.refl

-- ...and a bare `x` is not, because the context still owes the `+`.
rejectsX : runEnd (‵x ∷ []) tt
  Eq.≡ nothing {A = literal ‵x ⊗ literal ‵+} (‵x ∷ []) tt
rejectsX = Eq.refl
