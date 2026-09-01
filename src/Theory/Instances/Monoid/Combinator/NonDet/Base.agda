{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
-- `Core` at `ND`: return all parses.  `ND⊗r` is the one lemma that is not
-- a rename of `Incomplete`'s; `Ans-⊕&` is `appendND`, where `orElse`
-- commits to the left summand and loses parses.
open import Cubical.Foundations.Prelude
open import Cubical.WildCat.LocallySmall.Base
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.NonDet.Base
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt ; tt*)

open import Theory.Instances.Monoid.Combinator.Core Alphabet _≟_ public
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (_⊸_ ; ⊸-lam ; ⊸-lam⁻ ; ⊸-app)
open import Theory.Type.Monad.NonDet
  MonEqns Alphabet (λ _ → tt) listPresentation public
-- `Types` hides this `Δ` in favour of the one from `Strings`
import Theory.Type.SemanticAction.Base
  MonEqns Alphabet (λ _ → tt) listPresentation as SA

open WildCatNotation
open WildCatIso

private variable ℓA ℓB ℓC ℓD ℓK ℓL ℓX : Level

ℓG : Level
ℓG = ℓ-max ℓM ℓ

isSetListCode : {A : TheoryTy ℓA tt}
  → isSetTheoryTy A → isSetValued (ListCode A)
isSetListCode isSetA .fst = lift isSetBool
isSetListCode isSetA .snd false = lift (isSetLiftTheoryTy isSet⊤Ty)
isSetListCode isSetA .snd true = lift isSetA , lift tt*

isSetND : {A : TheoryTy ℓA tt} → isSetTheoryTy A → isSetTheoryTy (ND A)
isSetND {A = A} isSetA =
  isSetμ (λ _ → ListCode A) (λ _ → isSetListCode isSetA) tt

NDSet : TheorySet ℓA tt → TheorySet (ℓF ℓA) tt
NDSet (A , sA) = ND A , isSetND sA

fmapND : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} → A ⊢ B → ND A ⊢ ND B
fmapND = Monad.fmap NDMonad

-- Strength: using `A` once per list element is legal because the list's
-- `&` shares the string, so every element parses the same suffix.
ND⊗r : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} → A ⊗ ND B ⊢ ND (A ⊗ B)
ND⊗r {A = A} {B = B} = ⊸-lam⁻ (rec (λ _ → ListCode B) (λ _ → alg) tt)
  where
  alg : ⟦ ListCode B ⟧TheoryTy (λ _ → A ⊸ ND (A ⊗ B)) ⊢ A ⊸ ND (A ⊗ B)
  alg = ⊕ᴰ-elim λ where
    false → ⊸-lam (nilND ∘⊢ ⊤Ty-intro)
    true → ⊸-lam (cons (id⊢ ,⊗ (lowerTy ∘⊢ π₁))
                       (⊸-app ∘⊢ (id⊢ ,⊗ (lowerTy ∘⊢ π₂))))

nd-⊕& : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} → ND A & ND B ⊢ ND (A ⊕ B)
nd-⊕& = appendND ∘⊢ (fmapND inl ,&p fmapND inr)

semact-ND : {A : TheoryTy ℓA tt} {X : Type ℓX}
  → SemanticAction A X → SemanticAction (ND A) (List X)
semact-ND {A = A} {X = X} a = semact-rec alg tt
  where
  consA : ⟦ listBranch A true ⟧TheoryTy (λ _ → SA.Δ (List X)) ⊢ SA.Δ (List X)
  consA m (h , t) = (a m (h .lower) .fst ∷ t .lower .fst) , tt

  alg : ∀ _ → ⟦ ListCode A ⟧TheoryTy (λ _ → SA.Δ (List X)) ⊢ SA.Δ (List X)
  alg _ = ⊕ᴰ-elim λ where
    false → semact-pure []
    true → consA

-- where `Decidable` refutes, these return the empty enumeration

nd-lit⊗-at : (c : Alphabet) {K : TheorySet ℓK tt}
  → ty (▷ (NDSet K)) ⊢ ND (literal c ⊗ ty K)
nd-lit⊗-at c {K = K} = look⊗ br
  where
  br : (o : M₁) → ty (▷ (NDSet K)) & Λ₁ o ⊢ ND (literal c ⊗ ty K)
  br ε₁ = nilND ∘⊢ ⊤Ty-intro
  br (tk d) = go (d ≟ c)
    where
    go : (d Eq.≡ c) Sum.⊎ ((d Eq.≡ c) → Empty.⊥)
       → ty (▷ (NDSet K)) & Λ₁ (tk d) ⊢ ND (literal c ⊗ ty K)
    go (Sum.inl Eq.refl) = ND⊗r ∘⊢ (id⊢ ,⊗ π₁) ∘⊢ ▷⊗r c
    go (Sum.inr _) = nilND ∘⊢ ⊤Ty-intro

nd-char⊗-at : {K : TheorySet ℓK tt}
  → ty (▷ (NDSet K)) ⊢ ND (char ⊗ ty K)
nd-char⊗-at {K = K} = look⊗ br
  where
  br : (o : M₁) → ty (▷ (NDSet K)) & Λ₁ o ⊢ ND (char ⊗ ty K)
  br ε₁ = nilND ∘⊢ ⊤Ty-intro
  br (tk d) = ND⊗r ∘⊢ (σ⊕ d ,⊗ π₁) ∘⊢ ▷⊗r d

nd-ε : ⊤Ty ⊢ ND εTy
nd-ε = ⊕ᴰ-elim br ∘⊢ Λ-total
  where
  br : (o : M₁) → Λ₁ o ⊢ ND εTy
  br ε₁ = ηND ∘⊢ lowerTy
  br (tk c) = nilND ∘⊢ ⊤Ty-intro

NDAnswer : AnswerFunctor
NDAnswer .AnswerFunctor.ℓAns = ℓF
NDAnswer .AnswerFunctor.Ans = NDSet
NDAnswer .AnswerFunctor.Ans-≅ φ = fmapND (φ .fun)
NDAnswer .AnswerFunctor.Ans-⊕& = nd-⊕&
NDAnswer .AnswerFunctor.Ans-lit = nd-lit⊗-at
NDAnswer .AnswerFunctor.Ans-any = nd-char⊗-at
NDAnswer .AnswerFunctor.Ans-ε = nd-ε

NDCov : CovariantAnswer NDAnswer
NDCov .CovariantAnswer.Ans-map = fmapND
NDCov .CovariantAnswer.Ans-empty = nilND

NDLawful : LawfulAnswer NDAnswer
NDLawful .LawfulAnswer.Ans-≅-id = Monad.fmap-id NDMonad
NDLawful .LawfulAnswer.Ans-≅-⋆ φ ψ =
  sym (Monad.fmap-∘ NDMonad (ψ .fun) (φ .fun))

-- Routing at `ND` drops the branches not named rather than refuting them:
-- complete exactly when the route is correct.
NDDiv : DivariantAnswer NDAnswer
NDDiv = FromCov.div NDAnswer NDCov

NDCommitting : CommittingAnswer NDAnswer
NDCommitting = FromCov.committing NDAnswer NDCov

open Combinators NDAnswer public hiding (module Fix)
open LawfulCombinators NDAnswer NDLawful public
open CovCombinators NDAnswer NDCov public
open DivCombinators NDAnswer NDDiv public
open RoutedCombinators NDAnswer NDDiv NDCommitting public

Parses : TheoryTy ℓA tt → Type _
Parses A = ⊤Ty ⊢ ND A

module Fix {ℓA} (ℓK : Level) (A : TheorySet ℓA tt) where
  open Combinators.Fix NDAnswer ℓK A public

  parses : ty (▷ (ParserSet ℓ𝒦 ⟨□⟩ ⟨□⟩ A)) ⊢ Parser ℓ𝒦 ⟨□⟩ ⟨□⟩ A
    → Parses (ty A)
  parses = runFix
