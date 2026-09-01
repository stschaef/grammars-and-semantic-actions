{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `shift`/`runA` resist `Dec`: `Owes B = B ⊸ Goal` is an irrefutable
   universal inside the grammar; the derivative state fixes it. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Ascent.Decidability
  {ℓAlph} (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)) where

open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Combinator.Core Alphabet _≟_
open import Theory.Instances.Monoid.SequentialUnambiguity.Nullable Alphabet isSetAlphabet
  using (¬Nullable ; ¬Nullable-map)
open import Theory.Instances.Monoid.SequentialUnambiguity.First Alphabet isSetAlphabet
  using (¬Nullable-startsWith)
import Theory.Instances.Monoid.Combinator.Ascent.Base Alphabet _≟_ as A
import Theory.Instances.Monoid.Combinator.Decidable.Base Alphabet _≟_ ℓ-zero as D
open import Theory.Instances.Monoid.Derivative Alphabet isSetAlphabet
  using (Dl-string)
open import Theory.Instances.Monoid.Precise Alphabet isSetAlphabet
  using (Dl-absorb ; Dl-absorb⁻)
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using ( _⟜_ ; _⊸_ ; ⟜-precomp ; ⊸-lam ; ⊸-precomp ; ⊗ε-unit-r )

private variable ℓ : Level

-- shift has a converse once the state is a derivative, which `⊸⟜-swap` lacks.
shiftD : {A : TheoryTy ℓ tt} (c : Alphabet) (w : String)
  → literal c ⊗ Dl-string (w ++ (c ∷ [])) A ⊢ Dl-string w A
shiftD {A = A} = Dl-absorb {A = A}

shiftD⁻ : {A : TheoryTy ℓ tt} (c : Alphabet) (w : String)
  → Λ₁ (tk c) & Dl-string w A ⊢ literal c ⊗ Dl-string (w ++ (c ∷ [])) A
shiftD⁻ {A = A} = Dl-absorb⁻ {A = A}

-- Counterexample: `⊸⟜-swap` has no converse.  With stack `⊥Ty`,
-- `(⊥Ty ⟜ literal c) ⊸ ⊥Ty` holds vacuously at ε but the RHS demands a `c`.

module _ (c : Alphabet) where

  noStack : ⊥Ty ⟜ literal c ⊢ ⊥Ty
  noStack l s = s (⌈gen c ⌉) Eq.refl

  vacuous : εTy ⊢ (⊥Ty ⟜ literal c) ⊸ ⊥Ty
  vacuous =
    ⊸-lam {A = ⊥Ty ⟜ literal c} {B = εTy} {C = ⊥Ty} (noStack ∘⊢ ⊗ε-unit-r)

  notThere : ¬Nullable (literal c ⊗ (⊥Ty ⊸ ⊥Ty))
  notThere = ¬Nullable-map (⊗-map id⊢ ⊤Ty-intro) (¬Nullable-startsWith {c})

  -- Counterexample: so `Dec` cannot instantiate the ascent combinators as they stand.
  noShiftConverse :
    ((⊥Ty ⟜ literal c) ⊸ ⊥Ty ⊢ literal c ⊗ (⊥Ty ⊸ ⊥Ty)) → εTy ⊢ ⊥Ty
  noShiftConverse f = notThere ∘⊢ ((f ∘⊢ vacuous) ,& id⊢)


private variable ℓA ℓB ℓC ℓD : Level

module DivReduce (𝒯 : AnswerFunctor) (div : DivariantAnswer 𝒯)
  {ℓG : Level} (Goal : TheorySet ℓG tt) where
  open A.Ascent 𝒯 Goal
  open DivariantAnswer div

  reduce± : {ℓB ℓβ ℓA' : Level} {a c : ParserTag}
    {β : TheorySet ℓβ tt} {A : TheorySet ℓA' tt}
    → ty β ⊢ ty A → ty A ⊢ ty β
    → Asc ℓB a c β ⊢ Asc ℓB a c A
  reduce± {c = c} {β = β} {A = A} p q = mkA λ B →
    ▷map {t = c}
      (Ans-dimap {A = Owes (B A.⟜Set β)} {B = Owes (B A.⟜Set A)}
        (⊸-precomp {A = ty B ⟜ ty β} {A' = ty B ⟜ ty A} {C = ty Goal}
          (⟜-precomp {B = ty A} {B' = ty β} {C = ty B} p))
        (⊸-precomp {A = ty B ⟜ ty A} {A' = ty B ⟜ ty β} {C = ty Goal}
          (⟜-precomp {B = ty β} {B' = ty A} {C = ty B} q)))
    ∘⊢ aAt id⊢ B

module DecReduce = DivReduce D.DecAnswer D.DecDiv εSet
