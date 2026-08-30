-- Parser combinators inspired by agdarsec (Allais)
-- https://gallais.github.io/pdf/agdarsec18.pdf
-- These are total in the sense of Allais, we also have the additional strengths
-- 1. Our type system ensures that these are intrinsically sound parsers
-- 2. We are further showing below that we may have intrinsic *completeness* too
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `Core`'s combinators at `Dec`.  This is the instance that fixes `Core`'s
   shape: `DecTy A = A ⊕ ¬Ty A` is contravariant in the refutation, so
   `Ans-dimap` needs a map each way, and there is no `CovariantAnswer` --
   one cannot refuse to decide, so `fail` lands at `⊥Set` only.

   It is also the instance where `Ans-lit` does real work: `maybe-lit⊗-at`
   and `nd-lit⊗-at` fall through to a strength, whereas here a mismatch has
   to be *refuted*, which is what `Precise`'s `dec-lit⊗↑` and `Λ-disjoint`
   are for. -}
open import Cubical.Foundations.Prelude
open import Cubical.WildCat.LocallySmall.Base
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Decidable.Base
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Combinator.Core Alphabet _≟_ public
open import Theory.Instances.Monoid.Precise Alphabet isSetAlphabet public
  using (dec-lit⊗↑ ; dec-char⊗↑)
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⊗⊕ᴰ-distL ; &⊕ᴰ-distR)

open WildCatNotation
open WildCatIso

private variable ℓA ℓB ℓC ℓD ℓK ℓL : Level

ℓG : Level
ℓG = ℓ-max ℓM ℓ

dec-lit⊗-at : (c : Alphabet) {K : TheorySet ℓK tt}
  → ty (▷ (DecSet K)) ⊢ DecTy (literal c ⊗ ty K)
dec-lit⊗-at c {K = K} = look⊗ br
  where
  ¬fibre : (o : M₁) → (o Eq.≡ tk c → Empty.⊥)
    → ty (▷ (DecSet K)) & Λ₁ o ⊢ DecTy (literal c ⊗ ty K)
  ¬fibre o ne = dec-no ∘⊢ ⇒-intro
    (Λ-disjoint o (tk c) ne
      ∘⊢ ((π₂ ∘⊢ π₁) ,& ((id⊢ ,⊗ ⊤Ty-intro) ∘⊢ π₂)))

  br : (o : M₁) → ty (▷ (DecSet K)) & Λ₁ o ⊢ DecTy (literal c ⊗ ty K)
  br ε₁ = ¬fibre ε₁ (λ ())
  br (tk d) = onTokMatch (d ≟ c)
    where
    onTokMatch : (d Eq.≡ c) Sum.⊎ ((d Eq.≡ c) → Empty.⊥)
       → ty (▷ (DecSet K)) & Λ₁ (tk d) ⊢ DecTy (literal c ⊗ ty K)
    onTokMatch (Sum.inl Eq.refl) = dec-lit⊗↑ c ∘⊢ (id⊢ ,⊗ π₁) ∘⊢ ▷⊗r c
    onTokMatch (Sum.inr ne) = ¬fibre (tk d) (λ where Eq.refl → ne Eq.refl)

dec-char⊗-at : {K : TheorySet ℓK tt}
  → ty (▷ (DecSet K)) ⊢ DecTy (char ⊗ ty K)
dec-char⊗-at {K = K} = look⊗ br
  where
  ε-char : Λ₁ ε₁ & (char ⊗ ty K) ⊢ ⊥Ty
  ε-char = ⊕ᴰ-elim dis ∘⊢ &⊕ᴰ-distR ∘⊢ (id⊢ ,&p ⊗⊕ᴰ-distL)
    where
    dis : (d : Alphabet) → Λ₁ ε₁ & (literal d ⊗ ty K) ⊢ ⊥Ty
    dis d = Λ-disjoint ε₁ (tk d) (λ ()) ∘⊢ (id⊢ ,&p (id⊢ ,⊗ ⊤Ty-intro))

  br : (o : M₁) → ty (▷ (DecSet K)) & Λ₁ o ⊢ DecTy (char ⊗ ty K)
  br ε₁ = dec-no ∘⊢ ⇒-intro (ε-char ∘⊢ ((π₂ ∘⊢ π₁) ,& π₂))
  br (tk d) = dec-char⊗↑ ∘⊢ (σ⊕ d ,⊗ π₁) ∘⊢ ▷⊗r d


DecAnswer : AnswerFunctor
DecAnswer .AnswerFunctor.ℓAns ℓA = ℓA
DecAnswer .AnswerFunctor.Ans = DecSet
DecAnswer .AnswerFunctor.Ans-≅ φ = dec-map (φ .fun) (¬Ty-map (φ .inv))
DecAnswer .AnswerFunctor.Ans-⊕& = dec-⊕&
DecAnswer .AnswerFunctor.Ans-lit = dec-lit⊗-at
DecAnswer .AnswerFunctor.Ans-any = dec-char⊗-at
DecAnswer .AnswerFunctor.Ans-ε = dec-ε

DecDiv : DivariantAnswer DecAnswer
DecDiv .DivariantAnswer.Ans-dimap f g = dec-map f (¬Ty-map g)

-- The commitment, and the one field no covariant answer can supply: the
-- branch a route names may come back `no`, and the cover's `disjoint` is
-- what turns that refutation into a refutation of the whole sum.  `Maybe`
-- and `ND` reach the same *shape* through `FromCov.committing`, but by
-- discarding the other cells rather than by refuting them.
DecCommitting : CommittingAnswer DecAnswer
DecCommitting .CommittingAnswer.Ans-route sY Φ R decY =
  routeIn (λ y → ty (Φ y)) R decY

-- `Dec` is not a monad here, so the laws are `⊕`'s η and a case split.
-- `¬Ty-map id⊢ ≡ id⊢` and the two contravariant composites agree on the
-- nose, so both branches are `refl`.
DecLawful : LawfulAnswer DecAnswer
DecLawful .LawfulAnswer.Ans-≅-id = ⊕-η id⊢
DecLawful .LawfulAnswer.Ans-≅-⋆ φ ψ = funExt λ m → funExt λ where
  (Sum.inl a) → refl
  (Sum.inr na) → refl

open Combinators DecAnswer public hiding (module Fix ; module FixAll)
open LawfulCombinators DecAnswer DecLawful public
open DivCombinators DecAnswer DecDiv public
open RoutedCombinators DecAnswer DecDiv DecCommitting public

-- `Dec` transports a refutation, so this takes a map each way -- and the
-- two need not be inverse, which is why it is *not* `Core`'s `Ans-≅`.
▷dec-map : {t : ParserTag} {K : TheorySet ℓK tt} {L : TheorySet ℓL tt}
  → ty K ⊢ ty L → ty L ⊢ ty K
  → ty (▷? t (DecSet K)) ⊢ ty (▷? t (DecSet L))
▷dec-map = ▷Ans-dimap

▷dec-⊕& : {t : ParserTag} {K : TheorySet ℓK tt} {L : TheorySet ℓL tt}
  → ty (▷? t (DecSet K)) & ty (▷? t (DecSet L))
  ⊢ ty (▷? t (DecSet (K ⊕Set L)))
▷dec-⊕& = ▷Ans-⊕&

□dec-ε : {ℓK : Level} {D : TheoryTy ℓD tt} → D ⊢ ty (□ (DecSet (ε↑Set ℓK)))
□dec-ε = □Ans-ε

-- This is where the three instances genuinely differ, which is why `Core`
-- has no `mapP`.
mapP : {ℓK : Level} {a c : ParserTag} {A : TheorySet ℓA tt} {B : TheorySet ℓB tt}
  → ty A ⊢ ty B → ty B ⊢ ty A
  → Parser ℓK a c A ⊢ Parser ℓK a c B
mapP = mapP±

fail : {ℓK : Level} {a c : ParserTag} {D : TheoryTy ℓD tt}
  → D ⊢ Parser ℓK a c ⊥Set
fail {c = c} = mkP λ K → ▷next {t = c} (dec-no ∘⊢ ⇒-intro (⊗⊥-annihL ∘⊢ π₂))

module Fix {ℓA} (ℓK : Level) (A : TheorySet ℓA tt) where
  open Combinators.Fix DecAnswer ℓK A public

  decide : ty (▷ (ParserSet ℓ𝒦 ⟨□⟩ ⟨□⟩ A)) ⊢ Parser ℓ𝒦 ⟨□⟩ ⟨□⟩ A
    → Decidable (ty A)
  decide = runFix

module FixAll {ℓX ℓA} (ℓK : Level) {X : Type ℓX} (A : X → TheorySet ℓA tt) where
  open Combinators.FixAll DecAnswer ℓK A public

  decideAt : (ty (▷ Pall) ⊢ ty Pall) → (x : X) → Decidable (ty (A x))
  decideAt = runAt
