{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `Combinator/Core` at `Maybe`: at most one answer, no refutation.

   `Ans-⊕&` is `orElse`, which commits to the left -- so this is the PEG
   reading of a grammar, and an ambiguous one silently loses derivations.
   `Ans-node` ignores `Precise`: with nothing to refute, a node needs only
   the traversal. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
import Theory.Type.Later.Indexed as LI
module Theory.Combinator.Answer.Incomplete
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Sum as Sum

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.HLevels σeq V vs 𝒫
open import Theory.Type.Top.Base σeq V vs 𝒫
open import Theory.Type.Sum.Binary.Base σeq V vs 𝒫
open import Theory.Type.Product.Binary.Base σeq V vs 𝒫
open import Theory.Type.Monad.Base σeq V vs 𝒫
open import Theory.Type.Monad.Maybe σeq V vs 𝒫 public
open import Theory.Combinator.Core σeq V vs 𝒫 public

private variable ℓA ℓB : Level

-- The traversal `Ans-node` performs: every slot must answer.
travΠFin : {ℓp : Level} {n : ℕ} {P : Fin n → Type ℓp}
  → ((i : Fin n) → P i Sum.⊎ Unit)
  → ((i : Fin n) → P i) Sum.⊎ Unit
travΠFin {n = zero} d = Sum.inl λ ()
travΠFin {n = suc n} {P = P} d = onHead (d zero)
  where
  onTail : P zero → ((i : Fin n) → P (suc i)) Sum.⊎ Unit
    → ((i : Fin (suc n)) → P i) Sum.⊎ Unit
  onTail p (Sum.inl ps) = Sum.inl λ where
    zero → p
    (suc i) → ps i
  onTail p (Sum.inr _) = Sum.inr tt

  onHead : P zero Sum.⊎ Unit → ((i : Fin (suc n)) → P i) Sum.⊎ Unit
  onHead (Sum.inl p) = onTail p (travΠFin λ i → d (suc i))
  onHead (Sum.inr _) = Sum.inr tt

MaybeSet : {s : S} → TheorySet ℓA s → TheorySet ℓA s
MaybeSet (A , sA) = Maybe A , isSetMaybe sA

fmapM : {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  → A ⊢ B → Maybe A ⊢ Maybe B
fmapM = Monad.fmap MaybeMonad

MaybeAnswer : AnswerFunctor
MaybeAnswer .AnswerFunctor.ℓAns ℓA = ℓA
MaybeAnswer .AnswerFunctor.Ans = MaybeSet
MaybeAnswer .AnswerFunctor.Ans-map& f g m (Sum.inl a , h) = Sum.inl (f m (a , h))
MaybeAnswer .AnswerFunctor.Ans-map& f g m (Sum.inr u , h) = Sum.inr u
MaybeAnswer .AnswerFunctor.Ans-⊕& =
  orElse ∘⊢ (Monad.fmap MaybeMonad inl ,&p Monad.fmap MaybeMonad inr)
MaybeAnswer .AnswerFunctor.Ans-&& m (Sum.inl a , Sum.inl b) = Sum.inl (a , b)
MaybeAnswer .AnswerFunctor.Ans-&& m (Sum.inl a , Sum.inr u) = Sum.inr u
MaybeAnswer .AnswerFunctor.Ans-&& m (Sum.inr u , _) = Sum.inr u
MaybeAnswer .AnswerFunctor.Ans-ofDec m (Sum.inl a) = Sum.inl a
MaybeAnswer .AnswerFunctor.Ans-ofDec m (Sum.inr _) = Sum.inr tt
MaybeAnswer .AnswerFunctor.Ans-node o _ {ms = ms} ws = onAll (travΠFin ws)
  where
  onAll : _ → _
  onAll (Sum.inl all) = Sum.inl (node-mk all)
  onAll (Sum.inr _) = Sum.inr tt

-- `Maybe` is covariant, so both extra records come for free: a forward map
-- and `nothing`, which is a perfectly good answer at every grammar.  That
-- `nothing` is what makes routing cheap here -- the cells the route did not
-- name are simply not consulted, and no refutation is owed for them.
MaybeCov : CovariantAnswer MaybeAnswer
MaybeCov .CovariantAnswer.Ans-fmap = fmapM
MaybeCov .CovariantAnswer.Ans-empty = nothing

MaybeCommitting : CommittingAnswer MaybeAnswer
MaybeCommitting = FromCov.committing MaybeAnswer MaybeCov


module MaybeCombinators {ℓX ℓ<} {X : Type ℓX} (xs : X → S)
  (O : LI.IPtOrder σeq V vs 𝒫 xs ℓ<) where
  open Combinators MaybeAnswer xs O public

  test : {A : Fam ℓA} → Step A → (x : X) → ⊤Ty ⊢ Maybe (ty (A x))
  test = fix
