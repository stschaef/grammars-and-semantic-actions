{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `verified`: an intrinsically typed core term over the solved types, with
   erasure evidence.  One-directional: a backward map would owe completeness of unification. -}
open import Cubical.Foundations.Prelude
module Theory.Instances.Infer.Elaborate where

open import Cubical.Data.List using (List ; [] ; _∷_)
import Cubical.Data.List as List
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ ; discreteℕ)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Infer.Typing public

open import Theory.Type.SemanticAction.Base
  λEqns ℕ (λ _ → nm) termPresentation
import Theory.Instances.Lambda.Scope ℕ isSetℕ discreteℕ as LS
open LS using (DBTm ; dvar ; dapp ; dlam) public
import Theory.Combinator.Answer.Decidable
  λEqns ℕ (λ _ → nm) termPresentation as D
import Theory.Combinator.Answer.Incomplete
  λEqns ℕ (λ _ → nm) termPresentation as I
import Theory.Combinator.Answer.NonDet
  λEqns ℕ (λ _ → nm) termPresentation as N

module CD = Check D.DecAnswer
module CI = Check I.MaybeAnswer
module CN = Check N.NDAnswer

-- one unknown for the answer, then the term's block; the walk starts at offset one
closed : RawTm → Goal
closed t = scopeOf t , [] , mvar (scopeOf t) 0 , 1

-- The carried object: the recorded substitution, the elaborated core term,
-- and the erasure equation tying it to THIS source term.
Principal : (i : Goal) → RawTm → Type ℓ-zero
Principal (n , Γ , A , nx) t = Σ[ σ ∈ AList n ]
  Σ[ c ∈ Core (σ .fst) (mapCtx (applyA σ) Γ) (applyA σ A) ] (erase c ≡ t)

verified : (i : Goal) → ty (InfSet i) ⊢ Principal i
verified (n , Γ , A , nx) t (d , s) =
    mgu n (gen n Γ A nx t) s
  , sound (applyA (mgu n (gen n Γ A nx t) s))
          (applyFork (mgu n (gen n Γ A nx t) s .snd .snd))
          Γ A nx t d (mguUnifies n (gen n Γ A nx t) s)

Principal-ty : (i : Goal) → ty (InfSet i) ⊢ (λ _ → Σ[ m ∈ ℕ ] Tm m)
Principal-ty (n , Γ , A , nx) t (d , s) =
  mgu n (gen n Γ A nx t) s .fst , applyA (mgu n (gen n Γ A nx t) s) A

tyAction : (i : Goal) → SemanticAction (ty (InfSet i)) (Σ[ m ∈ ℕ ] Tm m)
tyAction i t d = Principal-ty i t d , tt

coreAction : (i : Goal)
  → SemanticAction (ty (InfSet i)) (Σ[ t ∈ RawTm ] Principal i t)
coreAction i t d = (t , verified i t d) , tt

shapeAction : (i : Goal) → SemanticAction (ty (GenSet i)) ℕ
shapeAction (n , Γ , A , nx) t d = nx , tt


infer : (i : Goal) → RawTm → Maybe (Σ[ m ∈ ℕ ] Tm m)
infer i = observe (CD.inferred (infM i)) (semact-dec (tyAction i))

inferTy : RawTm → Maybe (Σ[ m ∈ ℕ ] Tm m)
inferTy t = infer (closed t) t

inferCore : (i : Goal) → RawTm → Maybe (Σ[ u ∈ RawTm ] Principal i u)
inferCore i = observe (CD.inferred (infM i)) (semact-dec (coreAction i))

elaborate : (t : RawTm) → Maybe (Σ[ u ∈ RawTm ] Principal (closed t) u)
elaborate t = inferCore (closed t) t

-- scoping mode alone, so a test can see which conjunct refused
scopeOnly : (i : Goal) → RawTm → Maybe ℕ
scopeOnly i = observe (CD.inferred (genM i)) (semact-dec (shapeAction i))

-- ...the same run read as a verdict: total, so no `nothing` survives
shapeVerdict : (i : Goal) (t : RawTm) → GenOrNoCor i t
shapeVerdict i t = genVerdict i t (CD.inferred (genM i) t tt)

-- `Maybe`: the same source text with no refutation to propagate.
inferM : (i : Goal) → RawTm → Maybe (Σ[ m ∈ ℕ ] Tm m)
inferM i = observe (CI.inferred (infM i)) (semact-Maybe (tyAction i))

inferTyM : RawTm → Maybe (Σ[ m ∈ ℕ ] Tm m)
inferTyM t = inferM (closed t) t

-- `ND`: the answer's length observes that the judgment is a proposition.
private
  ndAction : (i : Goal)
    → SemanticAction (N.ND (ty (InfSet i))) (List (Σ[ m ∈ ℕ ] Tm m))
  ndAction i t nd = List.map (Principal-ty i t) (N.ndToList t nd) , tt

inferND : (i : Goal) → RawTm → List (Σ[ m ∈ ℕ ] Tm m)
inferND i = observe (CN.inferred (infM i)) (ndAction i)

inferTyND : RawTm → List (Σ[ m ∈ ℕ ] Tm m)
inferTyND t = inferND (closed t) t

-- Nameless core: `cvar` carries the `Lookup` the checker decided, `deBruijn`
-- counts it off.  `DBTm` is `Lambda/Scope`'s, shared with the other client.
nameless : {m : ℕ} {Γ : Ctx m} {A : Tm m} → Core m Γ A → LS.DBTm
nameless (cvar x v) = LS.dvar (deBruijn _ _ x v)
nameless (capp f a) = LS.dapp (nameless f) (nameless a)
nameless (clam x c) = LS.dlam (nameless c)

Readout : Type ℓ-zero
Readout = Σ[ m ∈ ℕ ] (Tm m × LS.DBTm)

elabAction : (i : Goal) → SemanticAction (ty (InfSet i)) Readout
elabAction (n , Γ , A , nx) t d =
  ( mgu n (gen n Γ A nx t) (d .snd) .fst
  , applyA (mgu n (gen n Γ A nx t) (d .snd)) A
  , nameless (verified (n , Γ , A , nx) t d .snd .fst) ) , tt

elabAt : (i : Goal) → RawTm → Maybe Readout
elabAt i = observe (CD.inferred (infM i)) (semact-dec (elabAction i))

elabTy : RawTm → Maybe Readout
elabTy t = elabAt (closed t) t
