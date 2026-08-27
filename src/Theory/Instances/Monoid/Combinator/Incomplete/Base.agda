-- Parser combinators inspired by agdarsec (Allais)
-- https://gallais.github.io/pdf/agdarsec18.pdf
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `Core`'s combinators at `Maybe`: the faithful adaptation of
   Danielsson/Allais.  A parser returns at most one parse and carries no
   refutation, so `mapP` needs only a forward map and `fail` exists at every
   grammar -- both come from `CovariantAnswer`.

   `Ans-⊕&` is `orElse`, which commits to the left summand.  That is the
   whole difference from `NonDet`, whose `Ans-⊕&` is `appendND`. -}
open import Cubical.Foundations.Prelude
open import Cubical.WildCat.LocallySmall.Base
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Incomplete.Base
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Combinator.Core Alphabet _≟_ public

open WildCatNotation
open WildCatIso

private variable ℓA ℓB ℓC ℓD ℓK ℓL : Level

ℓG : Level
ℓG = ℓ-max ℓM ℓ

MaybeSet : TheorySet ℓA tt → TheorySet ℓA tt
MaybeSet (A , sA) = Maybe A , isSetMaybe sA

fmapM : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} → A ⊢ B → Maybe A ⊢ Maybe B
fmapM = Monad.fmap MaybeMonad

-- The strength.  `Maybe` has at most one branch to push the `⊗`-factor
-- into, so this is `⊗⊕-distR`; `NonDet`'s counterpart has to traverse.
Maybe⊗r : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} → A ⊗ Maybe B ⊢ Maybe (A ⊗ B)
Maybe⊗r = ⊕-elim just (nothing ∘⊢ ⊤Ty-intro) ∘⊢ ⊗⊕-distR

maybe-⊕& : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → Maybe A & Maybe B ⊢ Maybe (A ⊕ B)
maybe-⊕& = orElse ∘⊢ (fmapM inl ,&p fmapM inr)

maybe-lit⊗-at : (c : Alphabet) {K : TheorySet ℓK tt}
  → ty (▷ (MaybeSet K)) ⊢ Maybe (literal c ⊗ ty K)
maybe-lit⊗-at c {K = K} = look⊗ br
  where
  br : (o : M₁) → ty (▷ (MaybeSet K)) & Λ₁ o ⊢ Maybe (literal c ⊗ ty K)
  br ε₁ = nothing ∘⊢ ⊤Ty-intro
  br (tk d) = go (d ≟ c)
    where
    go : (d Eq.≡ c) Sum.⊎ ((d Eq.≡ c) → Empty.⊥)
       → ty (▷ (MaybeSet K)) & Λ₁ (tk d) ⊢ Maybe (literal c ⊗ ty K)
    go (Sum.inl Eq.refl) = Maybe⊗r ∘⊢ (id⊢ ,⊗ π₁) ∘⊢ ▷⊗r c
    go (Sum.inr _) = nothing ∘⊢ ⊤Ty-intro

maybe-char⊗-at : {K : TheorySet ℓK tt}
  → ty (▷ (MaybeSet K)) ⊢ Maybe (char ⊗ ty K)
maybe-char⊗-at {K = K} = look⊗ br
  where
  br : (o : M₁) → ty (▷ (MaybeSet K)) & Λ₁ o ⊢ Maybe (char ⊗ ty K)
  br ε₁ = nothing ∘⊢ ⊤Ty-intro
  br (tk d) = Maybe⊗r ∘⊢ (σ⊕ d ,⊗ π₁) ∘⊢ ▷⊗r d

maybe-ε : ⊤Ty ⊢ Maybe εTy
maybe-ε = ⊕ᴰ-elim br ∘⊢ Λ-total
  where
  br : (o : M₁) → Λ₁ o ⊢ Maybe εTy
  br ε₁ = just ∘⊢ lowerTy
  br (tk c) = nothing ∘⊢ ⊤Ty-intro


MaybeAnswer : AnswerFunctor
MaybeAnswer .AnswerFunctor.ℓAns ℓA = ℓA
MaybeAnswer .AnswerFunctor.Ans = MaybeSet
MaybeAnswer .AnswerFunctor.Ans-≅ φ = fmapM (φ .fun)
MaybeAnswer .AnswerFunctor.Ans-⊕& = maybe-⊕&
MaybeAnswer .AnswerFunctor.Ans-lit = maybe-lit⊗-at
MaybeAnswer .AnswerFunctor.Ans-any = maybe-char⊗-at
MaybeAnswer .AnswerFunctor.Ans-ε = maybe-ε

MaybeCov : CovariantAnswer MaybeAnswer
MaybeCov .CovariantAnswer.Ans-map = fmapM
MaybeCov .CovariantAnswer.Ans-empty = nothing

-- `fmapM` is `bind (η ∘⊢ -)`, so both laws are the monad laws.
MaybeLawful : LawfulAnswer MaybeAnswer
MaybeLawful .LawfulAnswer.Ans-≅-id = Monad.fmap-id MaybeMonad
MaybeLawful .LawfulAnswer.Ans-≅-⋆ φ ψ =
  sym (Monad.fmap-∘ MaybeMonad (ψ .fun) (φ .fun))

-- Both derived, and both by discarding: `Ans-dimap` drops the backward map,
-- and `Ans-route` answers `nothing` at the cell it did not take.  So a
-- `Maybe` parser *can* be routed -- it just does not learn anything from
-- the route that `_<|>_` would not also have found by trying.
MaybeDiv : DivariantAnswer MaybeAnswer
MaybeDiv = FromCov.div MaybeAnswer MaybeCov

MaybeCommitting : CommittingAnswer MaybeAnswer
MaybeCommitting = FromCov.committing MaybeAnswer MaybeCov

open Combinators MaybeAnswer public hiding (module Fix)
open LawfulCombinators MaybeAnswer MaybeLawful public
open CovCombinators MaybeAnswer MaybeCov public
open DivCombinators MaybeAnswer MaybeDiv public
open RoutedCombinators MaybeAnswer MaybeDiv MaybeCommitting public

▷maybe-map : {t : ParserTag} {K : TheorySet ℓK tt} {L : TheorySet ℓL tt}
  → ty K ⊢ ty L → ty (▷? t (MaybeSet K)) ⊢ ty (▷? t (MaybeSet L))
▷maybe-map f = ▷map (fmapM f)

▷maybe-⊕& : {t : ParserTag} {K : TheorySet ℓK tt} {L : TheorySet ℓL tt}
  → ty (▷? t (MaybeSet K)) & ty (▷? t (MaybeSet L))
  ⊢ ty (▷? t (MaybeSet (K ⊕Set L)))
▷maybe-⊕& = ▷Ans-⊕&

□maybe-ε : {ℓK : Level} {D : TheoryTy ℓD tt} → D ⊢ ty (□ (MaybeSet (ε↑Set ℓK)))
□maybe-ε = □Ans-ε

Test : TheoryTy ℓA tt → Type _
Test A = ⊤Ty ⊢ Maybe A

module Fix {ℓA} (ℓK : Level) (A : TheorySet ℓA tt) where
  open Combinators.Fix MaybeAnswer ℓK A public

  -- ...which are then used to build tests
  test : ty (▷ (ParserSet ℓ𝒦 ⟨□⟩ ⟨□⟩ A)) ⊢ Parser ℓ𝒦 ⟨□⟩ ⟨□⟩ A → Test (ty A)
  test = runFix
