{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- One scope checker, three answers.

   `Scope.Check` is instantiated at `DecAnswer`, `MaybeAnswer` and
   `NDAnswer`; nothing in `Scope` changes.  The tests are `refl`, so they
   are run by the typechecker: the combinators, the guarded fixpoint and
   the three answers all reduce. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Lambda.ScopeTests where

open import Cubical.Data.Bool using (Bool ; true ; false ; false≢true)
import Cubical.Data.Empty as Empty
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ ; discreteℕ)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Sum as Sum

open import Theory.Instances.Lambda.Scope ℕ isSetℕ discreteℕ

import Theory.Combinator.Answer.Decidable
  λEqns ℕ (λ _ → nm) termPresentation as D
import Theory.Combinator.Answer.Incomplete
  λEqns ℕ (λ _ → nm) termPresentation as MB
import Theory.Combinator.Answer.NonDet
  λEqns ℕ (λ _ → nm) termPresentation as NDm

module CD = Check D.DecAnswer
module CM = Check MB.MaybeAnswer
module CN = Check NDm.NDAnswer

-- the same grammar, read three ways
decideScope : (Γ : Ctx) → D.Decidable (Scope Γ)
decideScope = CD.scoped

testScope : (Γ : Ctx) → ⊤Ty ⊢ MB.Maybe (Scope Γ)
testScope = CM.scoped

parsesScope : (Γ : Ctx) → ⊤Ty ⊢ NDm.ND (Scope Γ)
parsesScope = CN.scoped

-- readouts
decB : (Γ : Ctx) (t : RawTm) → Bool
decB Γ t = Sum.rec (λ _ → true) (λ _ → false) (decideScope Γ t tt)

mayB : (Γ : Ctx) (t : RawTm) → Bool
mayB Γ t = Sum.rec (λ _ → true) (λ _ → false) (testScope Γ t tt)

count : (Γ : Ctx) (t : RawTm) → ℕ
count Γ t = length (NDm.ndToList t (parsesScope Γ t tt))

-- some terms
idT : RawTm
idT = tlam 0 (tvar 0)

konst : RawTm
konst = tlam 0 (tlam 1 (tvar 0))

openT : RawTm
openT = tvar 0

capture : RawTm
capture = tlam 0 (tapp (tvar 0) (tvar 1))

selfApp : RawTm
selfApp = tlam 0 (tapp (tvar 0) (tvar 0))

-- ...and what each answer says about them
dec-id : decB [] idT ≡ true
dec-id = refl

dec-konst : decB [] konst ≡ true
dec-konst = refl

dec-selfApp : decB [] selfApp ≡ true
dec-selfApp = refl

dec-open : decB [] openT ≡ false
dec-open = refl

dec-open-in-ctx : decB (0 ∷ []) openT ≡ true
dec-open-in-ctx = refl

-- the binder really extends the context, and only for its own body
dec-capture : decB [] capture ≡ false
dec-capture = refl

dec-capture-in-ctx : decB (1 ∷ []) capture ≡ true
dec-capture-in-ctx = refl

-- shadowing: the inner `0` binds, so `tvar 0` is in scope
dec-shadow : decB [] (tlam 0 (tlam 0 (tvar 0))) ≡ true
dec-shadow = refl

-- `Maybe` agrees on all of them
may-id : mayB [] idT ≡ true
may-id = refl

may-open : mayB [] openT ≡ false
may-open = refl

may-capture : mayB [] capture ≡ false
may-capture = refl

may-capture-in-ctx : mayB (1 ∷ []) capture ≡ true
may-capture-in-ctx = refl

-- ...and `ND` enumerates exactly one derivation, because `Scope` is a
-- proposition: being in scope has no content beyond holding.
nd-id : count [] idT ≡ 1
nd-id = refl

nd-konst : count [] konst ≡ 1
nd-konst = refl

nd-open : count [] openT ≡ 0
nd-open = refl

nd-capture : count [] capture ≡ 0
nd-capture = refl

nd-capture-in-ctx : count (1 ∷ []) capture ≡ 1
nd-capture-in-ctx = refl

nd-selfApp : count [] selfApp ≡ 1
nd-selfApp = refl

-- The refutation is real content, not a bit: at `Dec` an out-of-scope term
-- comes back with a proof that it cannot be scoped.
no-open : D.¬Ty (Scope []) openT
no-open =
  Sum.rec (λ s → Empty.rec (false≢true s)) (λ n → n) (decideScope [] openT tt)
