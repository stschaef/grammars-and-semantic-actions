{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- THE FRONT END, AND WHAT A SUCCESSFUL RUN ACTUALLY HANDS BACK.

   `Typing`'s judgment at `infM` is thin -- a scoping derivation and a
   `Sol` -- and this file is where that stops mattering.  `verified` turns
   the pair into

     Σ[ σ ] Σ[ c ∈ Core (σΓ) (σA) ] (erase c ≡ t)

   an intrinsically typed core term over the SOLVED types, together with
   the evidence that it erases to the source.  So the composite really does
   reach `Annotated`'s discipline: having a derivation IS having the
   well-typed program, "the inferred type is a type of the term" is the
   type of a projection, and nothing here re-runs the checker to find out.

   The difference from `Annotated` is where the discipline comes from.
   There it is the DEFINITION of the judgment, so `Ans-map&`'s backward map
   owes -- and pays -- the converse.  Here it is a THEOREM (`Base`'s
   `sound`) applied after the fact, because the backward map would owe
   completeness of unification and `Unify/Correct` says exactly why that is
   not available.  `verified` is therefore one-directional by construction,
   which is the same shape as `Unify`'s own `verifiedTm` and for the same
   reason.

   All three answers.  Nothing in the composite needs `Ans-empty` or
   `Ans-route` -- the node cover is the free term algebra's, and the only
   non-node rule is a conjunction -- so `Dec`, `Maybe` and `ND` all run.
   At `ND` the answer is a singleton, which is `isPropGen` and `isPropSol`
   observed from outside; the unifier underneath is at `Dec` in all three
   cases, and that asymmetry is the join's price, argued in `Typing`. -}
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

-- The goal a closed term is inferred at: one unknown for the answer, then
-- the term's own block, and the walk starts at offset one.
closed : RawTm → Goal
closed t = scopeOf t , [] , mvar (scopeOf t) 0 , 1

-- THE CARRIED OBJECT.  A grammar, as in `Unify/Correct`'s `Unifier`: the
-- substitution the derivation records, the core term it elaborates to, and
-- the erasure equation that makes the core term be about THIS source term.
Principal : (i : Goal) → RawTm → Type ℓ-zero
Principal (n , Γ , A , nx) t = Σ[ σ ∈ AList n ]
  Σ[ c ∈ Core (σ .fst) (mapCtx (applyA σ) Γ) (applyA σ A) ] (erase c ≡ t)

verified : (i : Goal) → ty (InfSet i) ⊢ Principal i
verified (n , Γ , A , nx) t (d , s) =
    mgu n (gen n Γ A nx t) s
  , sound (applyA (mgu n (gen n Γ A nx t) s))
          (applyFork (mgu n (gen n Γ A nx t) s .snd .snd))
          Γ A nx t d (mguUnifies n (gen n Γ A nx t) s)

-- ...and the type on its own, which is what a test can compare.
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


-- The front ends: three internal terms composed, as everywhere else.
infer : (i : Goal) → RawTm → Maybe (Σ[ m ∈ ℕ ] Tm m)
infer i = observe (CD.inferred (infM i)) (semact-dec (tyAction i))

inferTy : RawTm → Maybe (Σ[ m ∈ ℕ ] Tm m)
inferTy t = infer (closed t) t

inferCore : (i : Goal) → RawTm → Maybe (Σ[ u ∈ RawTm ] Principal i u)
inferCore i = observe (CD.inferred (infM i)) (semact-dec (coreAction i))

elaborate : (t : RawTm) → Maybe (Σ[ u ∈ RawTm ] Principal (closed t) u)
elaborate t = inferCore (closed t) t

-- The scoping mode on its own, so that a test can see which of the two
-- conjuncts refused.
scopeOnly : (i : Goal) → RawTm → Maybe ℕ
scopeOnly i = observe (CD.inferred (genM i)) (semact-dec (shapeAction i))

-- ...and the same run read as a VERDICT rather than as an answer.  This is
-- what `Typing`'s `genCell` buys: not `Maybe`, but a shape derivation or a
-- proof that no intrinsically typed core term erases to `t` at any types
-- whatever.  It is total, so no `nothing` case survives to the caller.
shapeVerdict : (i : Goal) (t : RawTm) → GenOrNoCor i t
shapeVerdict i t = genVerdict i t (CD.inferred (genM i) t tt)

-- `Maybe`: the same source text with no refutation to propagate.
inferM : (i : Goal) → RawTm → Maybe (Σ[ m ∈ ℕ ] Tm m)
inferM i = observe (CI.inferred (infM i)) (semact-Maybe (tyAction i))

inferTyM : RawTm → Maybe (Σ[ m ∈ ℕ ] Tm m)
inferTyM t = inferM (closed t) t

-- `ND`: every derivation, so the length of the answer is an observation of
-- the judgment being a proposition.
private
  ndAction : (i : Goal)
    → SemanticAction (N.ND (ty (InfSet i))) (List (Σ[ m ∈ ℕ ] Tm m))
  ndAction i t nd = List.map (Principal-ty i t) (N.ndToList t nd) , tt

inferND : (i : Goal) → RawTm → List (Σ[ m ∈ ℕ ] Tm m)
inferND i = observe (CN.inferred (infM i)) (ndAction i)

inferTyND : RawTm → List (Σ[ m ∈ ℕ ] Tm m)
inferTyND t = inferND (closed t) t

-- ...and the core term read namelessly, which is the observation a `refl`
-- test can make of it.  The index is not recomputed: `cvar` carries the
-- `Lookup` the checker's `var` slot decided, and `deBruijn` counts it off,
-- exactly as `Annotated/Elaborate` and `Lambda/Nameless` do.  `DBTm` is
-- `Lambda/Scope`'s, so the two clients over this theory elaborate into the
-- same target.
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
