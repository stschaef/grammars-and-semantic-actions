{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Scope checking, and the nameless term it produces.

   The same shape as `Annotated/Elaborate`, one level simpler: a `Scope Γ`
   derivation folds to a de Bruijn term, and the variable case reads the
   index off the `InCtx` witness the checker already built.

   `compile` is three internal terms composed -- the checker
   `⊤Ty ⊢ DecTy (Scope Γ)`, the action `semact-dec` builds from `nameAction`,
   and `observe`, which is the single place a `⊤Ty`-map is read out.  There
   is no hand-rolled boundary. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no)
open SortedSig
open SortedEqns
module Theory.Instances.Lambda.Nameless where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ ; discreteℕ)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Sum as Sum

open import Theory.Instances.Lambda.Scope ℕ isSetℕ discreteℕ public

open import Theory.Type.SemanticAction.Base
  λEqns ℕ (λ _ → nm) termPresentation
import Theory.Combinator.Answer.Decidable
  λEqns ℕ (λ _ → nm) termPresentation as D

module CD = Check D.DecAnswer

-- Nameless terms.
data DBTm : Type ℓ-zero where
  dvar : ℕ → DBTm
  dapp : DBTm → DBTm → DBTm
  dlam : DBTm → DBTm

-- The fold.  Total on derivations: a derivation *is* the proof that every
-- name resolves, so there is no failure case.
toDB : (Γ : Ctx) (t : RawTm) → Scope Γ t → DBTm
toDB Γ (tvar x) v = dvar (deBruijn Γ x v)
toDB Γ (tapp t u) s = dapp (toDB Γ t (s .fst)) (toDB Γ u (s .snd))
toDB Γ (tlam x t) s = dlam (toDB (x ∷ Γ) t s)

nameAction : (Γ : Ctx) → SemanticAction (Scope Γ) DBTm
nameAction Γ t s = toDB Γ t s , tt

compile : (Γ : Ctx) → RawTm → Maybe DBTm
compile Γ = observe (CD.scoped Γ) (semact-dec (nameAction Γ))


-- Tests.  `refl`, so the typechecker runs scope checking and conversion.

idT konst shadow nested openT : RawTm
idT = tlam 0 (tvar 0)
konst = tlam 0 (tlam 1 (tvar 0))
shadow = tlam 0 (tlam 0 (tvar 0))
nested = tlam 0 (tlam 1 (tapp (tvar 0) (tvar 1)))
openT = tvar 0

db-id : compile [] idT ≡ just (dlam (dvar 0))
db-id = refl

-- the outer binder, so index 1
db-konst : compile [] konst ≡ just (dlam (dlam (dvar 1)))
db-konst = refl

-- ...and the same source name under a shadowing binder gives 0
db-shadow : compile [] shadow ≡ just (dlam (dlam (dvar 0)))
db-shadow = refl

db-nested : compile [] nested ≡ just (dlam (dlam (dapp (dvar 1) (dvar 0))))
db-nested = refl

db-open : compile [] openT ≡ nothing
db-open = refl

db-open-in-ctx : compile (0 ∷ []) openT ≡ just (dvar 0)
db-open-in-ctx = refl

db-open-deep : compile (5 ∷ 3 ∷ 0 ∷ []) openT ≡ just (dvar 2)
db-open-deep = refl
