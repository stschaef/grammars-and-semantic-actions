{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `Combinator/Core` at `Dec`.  The intrinsically correct answer: `DecTy A`
   *is* a decision, so a checker built from these combinators is sound and
   complete by typing rather than by a theorem.

   `Ans-node` is the only field that does real work, and `Precise o` is
   what it needs: a refutation of one argument refutes the node only when
   the node has no other decomposition. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
import Theory.Type.Later.Indexed as LI
module Theory.Combinator.Answer.Decidable
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
open import Cubical.Data.Empty using (⊥*)
import Cubical.Data.Equality as Eq

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.HLevels σeq V vs 𝒫
open import Theory.Type.Bottom.Base σeq V vs 𝒫
open import Theory.Type.Function.Base σeq V vs 𝒫
open import Theory.Type.Decidable.Base σeq V vs 𝒫 public
open import Theory.Type.Decidable.Route σeq V vs 𝒫 public
open import Theory.Combinator.Core σeq V vs 𝒫 public

private variable ℓA : Level

-- `¬Ty` lands in `⊥Ty`, which is `⊥*`; the search below speaks of `⊥`.
strip : {ℓp : Level} {P : Type ℓp}
  → P Sum.⊎ (P → ⊥* {ℓ-zero}) → P Sum.⊎ (P → Empty.⊥)
strip (Sum.inl p) = Sum.inl p
strip (Sum.inr np) = Sum.inr λ p → np p .lower

-- Deciding a finite conjunction.  `arities σ o` is `Fin (σ .arity o)`, so
-- this is the whole of the search `Ans-node` performs -- a node has no
-- other quantifier.
decΠFin : {ℓp : Level} {n : ℕ} {P : Fin n → Type ℓp}
  → ((i : Fin n) → P i Sum.⊎ (P i → Empty.⊥))
  → ((i : Fin n) → P i) Sum.⊎ (((i : Fin n) → P i) → Empty.⊥)
decΠFin {n = zero} d = Sum.inl λ ()
decΠFin {n = suc n} {P = P} d = onHead (d zero)
  where
  onTail : P zero
    → ((i : Fin n) → P (suc i)) Sum.⊎ (((i : Fin n) → P (suc i)) → Empty.⊥)
    → ((i : Fin (suc n)) → P i) Sum.⊎ (((i : Fin (suc n)) → P i) → Empty.⊥)
  onTail p (Sum.inl ps) = Sum.inl λ where
    zero → p
    (suc i) → ps i
  onTail p (Sum.inr nps) = Sum.inr λ f → nps λ i → f (suc i)

  onHead : P zero Sum.⊎ (P zero → Empty.⊥)
    → ((i : Fin (suc n)) → P i) Sum.⊎ (((i : Fin (suc n)) → P i) → Empty.⊥)
  onHead (Sum.inl p) = onTail p (decΠFin λ i → d (suc i))
  onHead (Sum.inr np) = Sum.inr λ f → np (f zero)

DecAnswer : AnswerFunctor
DecAnswer .AnswerFunctor.ℓAns ℓA = ℓA
DecAnswer .AnswerFunctor.Ans = DecSet
DecAnswer .AnswerFunctor.Ans-map& f g m (Sum.inl a , h) = Sum.inl (f m (a , h))
DecAnswer .AnswerFunctor.Ans-map& f g m (Sum.inr n , h) = Sum.inr λ b → n (g m (b , h))
DecAnswer .AnswerFunctor.Ans-⊕& = dec-⊕&
DecAnswer .AnswerFunctor.Ans-&& m (Sum.inl a , Sum.inl b) = Sum.inl (a , b)
DecAnswer .AnswerFunctor.Ans-&& m (Sum.inl a , Sum.inr nb) = Sum.inr λ z → nb (z .snd)
DecAnswer .AnswerFunctor.Ans-&& m (Sum.inr na , _) = Sum.inr λ z → na (z .fst)
DecAnswer .AnswerFunctor.Ans-ofDec = id⊢
DecAnswer .AnswerFunctor.Ans-node o prec {As = As} {ms = ms} ws =
  onAll (decΠFin (λ a → strip (ws a)))
  where
  Slots : interpIn o ↓M → Type _
  Slots mz = (a : arities σ o) → ty (As mz a) (mz a)

  -- Every decomposition of `op o ms` is `ms`, so a refutation of one slot
  -- at `ms` refutes the node outright.  This is the whole use of `Precise`.
  atMs : ty (⊗ᴰSet o As) (op o ms) → Slots ms
  atMs (ms' , e' , ws') =
    subst Slots (cong fst (prec (op o ms) (ms' , e') (ms , Eq.refl))) ws'

  onAll : Slots ms Sum.⊎ (Slots ms → Empty.⊥)
    → ty (DecSet (⊗ᴰSet o As)) (op o ms)
  onAll (Sum.inl all) = Sum.inl (node-mk all)
  onAll (Sum.inr no) = Sum.inr λ t → Empty.rec (no (atMs t))

-- Committing at `Dec`, which is exactly `routeIn`.  `Maybe` and `ND` reach
-- the same shape through `FromCov.committing`, but by the opposite
-- argument: they drop the cells they did not take, and this one refutes
-- them.  `DecAnswer` has no `CovariantAnswer` -- `Ans-empty` would be a
-- uniform decision procedure at every grammar -- so the derivation is not
-- available and the field is discharged directly.
DecCommitting : CommittingAnswer DecAnswer
DecCommitting .CommittingAnswer.Ans-route sY Φ R decY =
  routeIn (λ y → ty (Φ y)) R decY


module DecCombinators {ℓX ℓ<} {X : Type ℓX} (xs : X → S)
  (O : LI.IPtOrder σeq V vs 𝒫 xs ℓ<) where
  open Combinators DecAnswer xs O public

  -- what a checker at `Dec` is: a decision procedure at each index
  decide : {A : Fam ℓA} → Step A → (x : X) → Decidable (ty (A x))
  decide = fix
