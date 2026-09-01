{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `Bidir` is `Annotated` minus the application's argument type; folding a
   derivation reproduces the `Annotated` term: the annotation is read off the route's commitment. -}
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

-- Total on derivations; in the application case `dom C` is the annotation, and `C` came from the route.
elab : (Γ : Ctx) (A : Ty) (t : BTm) → Chk Γ A t → ATm
elab Γ A (bvar x) w = avar x
elab Γ A (bapp f a) (C , _ , df , da) =
  aapp (dom C) (elab Γ C f df) (elab Γ (dom C) a da)
elab Γ A (blam x B t) (_ , dt) =
  alam x B (elab ((x , B) ∷ Γ) (cod A) t dt)

chkAction : (Γ : Ctx) (A : Ty) → SemanticAction (Chk Γ A) ATm
chkAction Γ A t d = elab Γ A t d , tt

synAction : (Γ : Ctx) → SemanticAction (ty (SynSet Γ)) (Ty × ATm)
synAction Γ t (A , d) = (A , elab Γ A t d) , tt

check : (Γ : Ctx) (A : Ty) → BTm → Maybe ATm
check Γ A = observe (CD.bidir (chkM Γ A)) (semact-dec (chkAction Γ A))

synth : (Γ : Ctx) → BTm → Maybe (Ty × ATm)
synth Γ = observe (CD.bidir (synM Γ)) (semact-dec (synAction Γ))

checkM : (Γ : Ctx) (A : Ty) → BTm → Maybe ATm
checkM Γ A = observe (CI.bidir (chkM Γ A)) (semact-Maybe (chkAction Γ A))

synthM : (Γ : Ctx) → BTm → Maybe (Ty × ATm)
synthM Γ = observe (CI.bidir (synM Γ)) (semact-Maybe (synAction Γ))

-- `ND`: the answer's length is an observation of unambiguity.
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
