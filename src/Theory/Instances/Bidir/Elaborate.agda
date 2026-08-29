{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- ELABORATION RECOVERS THE ANNOTATION.

   `Bidir` is `Annotated` with the application's argument type deleted, and
   a derivation in `Bidir` is a proof-relevant object: its application case
   carries the type the route committed to.  Folding it therefore does not
   merely say "this term is well typed" -- it produces the `Annotated` term
   whose annotation was dropped, on the nose.  `elab` below lands in
   `Annotated/Base`'s own `ATm`, and `Tests` feeds the result back into
   `Annotated/Elaborate`'s checker, which accepts it.

   That is the whole content of "bidirectional typing is elaboration": the
   annotation is not guessed by a heuristic and it is not recomputed, it is
   READ OFF the derivation, and the thing that put it there is the `Route`.

   Three answers, all three available.  `Dec` gets it through `routeIn`,
   which spends the route's `disjoint` to refute the alternatives it did
   not take; `Maybe` and `ND` through `FromCov.committing`, which discards
   them with `Ans-empty` instead.  At `ND` the readout is the LIST of
   derivations, so its length is an observation of unambiguity: every test
   below returns a singleton, which is `isPropChk` seen from outside. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Bidir.Elaborate where

open import Cubical.Data.List using (List ; [] ; _∷_)
import Cubical.Data.List as List
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Sum as Sum

open import Theory.Instances.Bidir.Typing public

open import Theory.Type.SemanticAction.Base
  BEqns ℕ (λ _ → nm) bPresentation
import Theory.Combinator.Answer.Decidable
  BEqns ℕ (λ _ → nm) bPresentation as D
import Theory.Combinator.Answer.Incomplete
  BEqns ℕ (λ _ → nm) bPresentation as I
import Theory.Combinator.Answer.NonDet
  BEqns ℕ (λ _ → nm) bPresentation as N

module CD = Check D.DecAnswer D.DecCommitting
module CI = Check I.MaybeAnswer I.MaybeCommitting
module CN = Check N.NDAnswer N.NDCommitting

-- The fold.  No failure case: a derivation is a proof the term checks, so
-- elaboration is total on derivations.  The application case is the one
-- that has something to say -- `dom C` is the annotation, and `C` came
-- from the route.
elab : (Γ : Ctx) (A : Ty) (t : BTm) → Chk Γ A t → ATm
elab Γ A (bvar x) w = avar x
elab Γ A (bapp f a) (C , _ , df , da) =
  aapp (dom C) (elab Γ C f df) (elab Γ (dom C) a da)
elab Γ A (blam x B t) (_ , dt) =
  alam x B (elab ((x , B) ∷ Γ) (cod A) t dt)

chkAction : (Γ : Ctx) (A : Ty) → SemanticAction (Chk Γ A) ATm
chkAction Γ A t d = elab Γ A t d , tt

-- ...and at the synthesis mode the readout carries the type as well, since
-- the derivation there is the pair `(A , Γ ⊢ t ⇐ A)`.
synAction : (Γ : Ctx) → SemanticAction (ty (SynSet Γ)) (Ty × ATm)
synAction Γ t (A , d) = (A , elab Γ A t d) , tt

-- The front ends: three internal terms composed, as in `Annotated`.
check : (Γ : Ctx) (A : Ty) → BTm → Maybe ATm
check Γ A = observe (CD.bidir (chkM Γ A)) (semact-dec (chkAction Γ A))

synth : (Γ : Ctx) → BTm → Maybe (Ty × ATm)
synth Γ = observe (CD.bidir (synM Γ)) (semact-dec (synAction Γ))

-- `Maybe`: the same front end with no refutation to propagate.
checkM : (Γ : Ctx) (A : Ty) → BTm → Maybe ATm
checkM Γ A = observe (CI.bidir (chkM Γ A)) (semact-Maybe (chkAction Γ A))

synthM : (Γ : Ctx) → BTm → Maybe (Ty × ATm)
synthM Γ = observe (CI.bidir (synM Γ)) (semact-Maybe (synAction Γ))

-- `ND`: every derivation, so the length of the answer is an observation of
-- unambiguity.
private
  ndAction : (Γ : Ctx) (A : Ty)
    → SemanticAction (N.ND (Chk Γ A)) (List ATm)
  ndAction Γ A t nd = List.map (elab Γ A t) (N.ndToList t nd) , tt

  ndSynAction : (Γ : Ctx)
    → SemanticAction (N.ND (ty (SynSet Γ))) (List (Ty × ATm))
  ndSynAction Γ t nd =
    List.map (λ d → d .fst , elab Γ (d .fst) t (d .snd)) (N.ndToList t nd) , tt

checkND : (Γ : Ctx) (A : Ty) → BTm → List ATm
checkND Γ A = observe (CN.bidir (chkM Γ A)) (ndAction Γ A)

synthND : (Γ : Ctx) → BTm → List (Ty × ATm)
synthND Γ = observe (CN.bidir (synM Γ)) (ndSynAction Γ)
