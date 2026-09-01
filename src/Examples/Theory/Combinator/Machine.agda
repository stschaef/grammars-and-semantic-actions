{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The same parser `px`, cut against two configurations, recognises two different
   languages: a configuration is the context the parser runs in. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Examples.Theory.Combinator.Machine where

open import Cubical.Data.List using ([] ; _∷_)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Unit using (tt ; tt*)

open import Theory.Instances.Monoid.Combinator.ExprGrammar
open import Theory.Instances.Monoid.Combinator.Core Tk _≟K_
import Theory.Instances.Monoid.Combinator.Incomplete.Base Tk _≟K_ ℓ-zero as Inc
import Theory.Instances.Monoid.Combinator.Machine Tk _≟K_ as Mch

open Combinators Inc.MaybeAnswer using (Parser ; tok ; pmore ; □Ans-ε)
open CovCombinators Inc.MaybeAnswer Inc.MaybeCov using (mapP)

px : ⊤Ty ⊢ Parser ℓM ⟨□⟩ ⟨□⟩ (litSet ‵x)
px = pmore ∘⊢ tok ‵x

-- both configurations answer to the same goal: a `Maybe` of the whole `x +`
module R = Mch.Runner Inc.MaybeAnswer {ℓK = ℓ-zero} {A = litSet ‵x ⊗Set litSet ‵+}

-- context 1: nothing follows (`K = ε`), so the parse must END after `x +`
ctxEnd : ⊤Ty ⊢ R.Config (ℓ-max ℓM ℓ-zero) ⟨□⟩ ⟨□⟩ (litSet ‵x ⊗Set litSet ‵+)
ctxEnd = R.initial

-- context 2: a `+` still owed, pushed onto `K`; expects only an `x`
ctxPlus : ⊤Ty ⊢ R.Config _ ⟨□⟩ ⟨□⟩ (litSet ‵x)
ctxPlus = R.push (pmore ∘⊢ tok ‵+) R.initial ∘⊢ (id⊢ ,& id⊢)

runEnd : ⊤Ty ⊢ ty (Inc.MaybeSet (litSet ‵x ⊗Set litSet ‵+))
runEnd = R.cut ∘⊢ (px ,& ctxPlus)

-- `x +` accepted: the pending `+` is discharged from `K`; `Eq.refl` is the whole check
acceptsXPlus :
  runEnd (‵x ∷ ‵+ ∷ []) tt
  Eq.≡ just {A = literal ‵x ⊗ literal ‵+} (‵x ∷ ‵+ ∷ [])
         (two (‵x ∷ []) (‵+ ∷ []) , Eq.refl , (Eq.refl , (Eq.refl , tt*)))
acceptsXPlus = Eq.refl

-- a bare `x` is rejected: the context still owes the `+`
rejectsX : runEnd (‵x ∷ []) tt
  Eq.≡ nothing {A = literal ‵x ⊗ literal ‵+} (‵x ∷ []) tt
rejectsX = Eq.refl
