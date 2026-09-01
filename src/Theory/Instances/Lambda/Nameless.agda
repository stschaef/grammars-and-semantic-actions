{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Scope checking and its nameless readout: `Scope Γ t` is
   `Σ[ d ∈ DBTm ] Names Γ d t`, so `toDB = fst`.  No fold. -}
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

toDB : (Γ : Ctx) (t : RawTm) → Scope Γ t → DBTm
toDB Γ t = fst

nameRight : (Γ : Ctx) (t : RawTm) (s : Scope Γ t) → Names Γ (toDB Γ t s) t
nameRight Γ t = snd

nameAction : (Γ : Ctx) → SemanticAction (Scope Γ) DBTm
nameAction Γ t s = toDB Γ t s , tt

compile : (Γ : Ctx) → RawTm → Maybe DBTm
compile Γ = observe (CD.scoped Γ) (semact-dec (nameAction Γ))

idT konst shadow nested openT : RawTm
idT = tlam 0 (tvar 0)
konst = tlam 0 (tlam 1 (tvar 0))
shadow = tlam 0 (tlam 0 (tvar 0))
nested = tlam 0 (tlam 1 (tapp (tvar 0) (tvar 1)))
openT = tvar 0

db-id : compile [] idT ≡ just (dlam (dvar 0))
db-id = refl

db-konst : compile [] konst ≡ just (dlam (dlam (dvar 1)))
db-konst = refl

-- shadowing resolves inward: the same source name gives 0
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

-- a repeated name resolves to the inner binding (the content of `At`)
db-shadowed-ctx : compile (0 ∷ 0 ∷ []) openT ≡ just (dvar 0)
db-shadowed-ctx = refl
