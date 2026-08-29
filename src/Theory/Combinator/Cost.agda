{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Cost, as a grading on any answer.
   
   `bc4d6a4` got the monoid tokeniser linear and recorded it as a doubling
   table in a commit message.  A table is *evidence*; the claim it is
   evidence for has no home in the tree, because the framework has no cost
   model.  This is one.

   Cost is not a rival notion of answer -- it is a grading on whatever
   answer you already have.  So this is a TRANSFORMER, not a fourth
   backend: `Costed 𝒯` runs exactly the grammar `𝒯` runs and pairs the
   result with a step count, so all ten clients get it at once and the
   count is guaranteed to describe the same computation the checker did.

   What a step is, chosen so the count is honest about the thing we
   actually worry about:

     `Ans-node`    1 + the slots' costs   -- one step per node
     `Ans-ofDec`   1                      -- one step per side condition
     `Ans-⊕&`      c₁ + c₂                -- ALTERNATION PAYS FOR BOTH
     `Ans-&&`      c₁ + c₂                -- so does conjunction
     `Ans-map&`    unchanged              -- relabelling is bookkeeping
     `Ans-re`      1                      -- but see the blind spot below

   The `Ans-⊕&` line is the point.  Nested `_<|>_` at `Dec` is exponential,
   and every client avoids it by committing through a cover instead.  That
   was argued on grounds of internality; here it becomes arithmetic.

   THE BLIND SPOT, stated up front because it is not small.  This counts
   the framework's own steps, not Agda's normalisation.  Two things it
   cannot see:

     * `Ans-re`'s `f` is applied to the MODEL ELEMENT, outside the answer.
       `Unify`'s `applyStack` rewrites the whole stack and is charged 1.
     * conversion checking.  `PatComp/Tests` spent 25 minutes in
       `DecAnswer =?= MaybeAnswer` under `--lossy-unification`, which is
       ZERO steps here.

   So this gives a checkable claim about THE ALGORITHM YOU WROTE and says
   nothing about THE PROGRAM AGDA RUNS.  The doubling table does not go
   away; it becomes the thing you validate this model against. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Combinator.Cost
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; isSetℕ)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.HLevels σeq V vs 𝒫
open import Theory.Type.Top.Base σeq V vs 𝒫
open import Theory.Combinator.Core σeq V vs 𝒫

private variable ℓA ℓB ℓH ℓp : Level

private
  sumFin : {n : ℕ} → (Fin n → ℕ) → ℕ
  sumFin {zero} f = 0
  sumFin {suc n} f = f zero + sumFin (λ i → f (suc i))

-- The grading.  `Costed 𝒯` is `𝒯` with a step count riding alongside.
module Costed (𝒯 : AnswerFunctor) where
  private module T = AnswerFunctor 𝒯

  CostSet : {s : S} → TheorySet ℓA s → TheorySet (T.ℓAns ℓA) s
  CostSet A = (λ m → ℕ × ty (T.Ans A) m)
            , λ m → isSet× isSetℕ (isSetTy (T.Ans A) m)

  costed : AnswerFunctor
  costed .AnswerFunctor.ℓAns = T.ℓAns
  costed .AnswerFunctor.Ans = CostSet
  costed .AnswerFunctor.Ans-map& f g m ((c , a) , h) =
    c , T.Ans-map& f g m (a , h)
  costed .AnswerFunctor.Ans-⊕& m ((c₁ , a) , (c₂ , b)) =
    c₁ + c₂ , T.Ans-⊕& m (a , b)
  costed .AnswerFunctor.Ans-&& m ((c₁ , a) , (c₂ , b)) =
    c₁ + c₂ , T.Ans-&& m (a , b)
  costed .AnswerFunctor.Ans-ofDec m d = 1 , T.Ans-ofDec m d
  costed .AnswerFunctor.Ans-node o prec ws =
    suc (sumFin (λ a → ws a .fst)) , T.Ans-node o prec (λ a → ws a .snd)
  costed .AnswerFunctor.Ans-re f m (c , a) = suc c , T.Ans-re f m a

  -- reading the count off a checker built at `costed`
  stepsOf : {s : S} {A : TheorySet ℓA s}
    → (⊤Ty ⊢ ty (CostSet A)) → ↓M s → ℕ
  stepsOf p m = p m _ .fst

  answerOf : {s : S} {A : TheorySet ℓA s}
    → (⊤Ty ⊢ ty (CostSet A)) → ⊤Ty ⊢ ty (T.Ans A)
  answerOf p m u = p m u .snd
