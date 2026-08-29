{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `Combinator/Core` at `ND`: every answer, not just one.

   `Ans-⊕&` is `appendND` where `Incomplete`'s is `orElse`, so an ambiguous
   grammar keeps all its derivations.  `Ans-node` is the cartesian product
   of the slots' enumerations -- the one place where the monoid version's
   binary `ND⊗r` becomes genuinely n-ary, since an operation has as many
   arguments as it has.

   As in the monoid development, completeness here is a claim about the
   grammar and not a consequence of the type: `ND A` is a list of parses
   and nothing types "these are all of them".  Only `Dec` is intrinsic. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
import Theory.Type.Later.Indexed as LI
module Theory.Combinator.Answer.NonDet
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_) renaming (map to mapL)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)
import Cubical.Data.Sum as Sum

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.HLevels σeq V vs 𝒫
open import Theory.Type.Top.Base σeq V vs 𝒫
open import Theory.Type.Sum.Base σeq V vs 𝒫
open import Theory.Type.Sum.Binary.Base σeq V vs 𝒫
open import Theory.Type.Product.Binary.Base σeq V vs 𝒫
open import Theory.Type.Inductive.Base σeq V vs 𝒫
open import Theory.Type.Inductive.HLevels σeq V vs 𝒫
open import Theory.Type.Monad.Base σeq V vs 𝒫
open import Theory.Type.Monad.NonDet σeq V vs 𝒫 public
open import Theory.Combinator.Core σeq V vs 𝒫 public

private variable ℓA ℓp ℓq : Level

private
  concatMapL : {A : Type ℓp} {B : Type ℓq} → (A → List B) → List A → List B
  concatMapL f [] = []
  concatMapL f (a ∷ as) = f a ++ concatMapL f as

-- The cartesian product of the slots.  `arities σ o` is `Fin (σ .arity o)`,
-- so a node's enumeration is this fold over its arity.
allΠFin : {n : ℕ} {P : Fin n → Type ℓp}
  → ((i : Fin n) → List (P i)) → List ((i : Fin n) → P i)
allΠFin {n = zero} f = (λ ()) ∷ []
allΠFin {n = suc n} {P = P} f =
  concatMapL (λ h → mapL (glue h) (allΠFin λ i → f (suc i))) (f zero)
  where
  glue : P zero → ((i : Fin n) → P (suc i)) → (i : Fin (suc n)) → P i
  glue h t zero = h
  glue h t (suc i) = t i

-- `ND` is a `μ`, so its elements are lists; these two are the isomorphism,
-- used only to reach `allΠFin` and come back.
ndToList : {s : S} {A : TheoryTy ℓA s} → ND A ⊢ (λ m → List (A m))
ndToList {s = s} {A = A} = rec (λ _ → ListCode A) (λ _ → alg) tt
  where
  Lst : Unit → TheoryTy _ s
  Lst _ m = List (A m)

  alg : ⟦ ListCode A ⟧TheoryTy Lst ⊢ Lst tt
  alg = ⊕ᴰ-elim λ where
    false → λ m _ → []
    true → λ m z → z .fst .lower ∷ z .snd .lower

ndFromList : {s : S} {A : TheoryTy ℓA s} (m : ↓M s) → List (A m) → ND A m
ndFromList m [] = nilND m tt
ndFromList m (a ∷ l) = consND m (a , ndFromList m l)

isSetListCode : {s : S} {A : TheoryTy ℓA s}
  → isSetTheoryTy A → isSetValued (ListCode A)
isSetListCode isSetA .fst = lift isSetBool
isSetListCode isSetA .snd false = lift (isSetLiftTheoryTy isSet⊤Ty)
isSetListCode isSetA .snd true = lift isSetA , lift tt*

isSetND : {s : S} {A : TheoryTy ℓA s} → isSetTheoryTy A → isSetTheoryTy (ND A)
isSetND {A = A} isSetA =
  isSetμ (λ _ → ListCode A) (λ _ → isSetListCode isSetA) tt

NDSet : {s : S} → TheorySet ℓA s → TheorySet (ℓF ℓA) s
NDSet (A , sA) = ND A , isSetND sA

NDAnswer : AnswerFunctor
NDAnswer .AnswerFunctor.ℓAns = ℓF
NDAnswer .AnswerFunctor.Ans = NDSet
NDAnswer .AnswerFunctor.Ans-map& f g m (x , h) =
  ndFromList m (mapL (λ a → f m (a , h)) (ndToList m x))
NDAnswer .AnswerFunctor.Ans-⊕& =
  appendND ∘⊢ (Monad.fmap NDMonad inl ,&p Monad.fmap NDMonad inr)
NDAnswer .AnswerFunctor.Ans-&& m (x , y) = ndFromList m
  (concatMapL (λ a → mapL (λ b → a , b) (ndToList m y)) (ndToList m x))
NDAnswer .AnswerFunctor.Ans-ofDec m (Sum.inl a) = ηND m a
NDAnswer .AnswerFunctor.Ans-ofDec m (Sum.inr _) = nilND m tt
NDAnswer .AnswerFunctor.Ans-node o _ {ms = ms} ws =
  ndFromList (op o ms) (mapL node-mk (allΠFin λ a → ndToList (ms a) (ws a)))
-- the derivations of `A` at `f m` are the derivations of `A ∘ f` at `m`,
-- and `ND` is a list of them
NDAnswer .AnswerFunctor.Ans-re f m x = ndFromList m (ndToList (f m) x)

-- `ND` is covariant too, with `nilND` for the empty answer -- and here the
-- empty answer is literally the empty list of derivations.  Routing at `ND`
-- therefore *counts*: the cells the route did not name contribute nothing,
-- and the count that comes back is the number of derivations the named cell
-- admits.  That is what makes `ND` the backend that detects a route whose
-- `disjoint` is a lie; see `Instances/Class/Resolve`.
NDCov : CovariantAnswer NDAnswer
NDCov .CovariantAnswer.Ans-fmap = Monad.fmap NDMonad
NDCov .CovariantAnswer.Ans-empty = nilND

NDCommitting : CommittingAnswer NDAnswer
NDCommitting = FromCov.committing NDAnswer NDCov


module NDCombinators {ℓX ℓ<} {X : Type ℓX} (xs : X → S)
  (O : LI.IPtOrder σeq V vs 𝒫 xs ℓ<) where
  open Combinators NDAnswer xs O public

  parses : {A : Fam ℓA} → Step A → (x : X) → ⊤Ty ⊢ ND (ty (A x))
  parses = fix
