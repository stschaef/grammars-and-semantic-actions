{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The Kleene fold by guarded recursion, so no `TERMINATING` is asserted.

   `KleeneStar.fold*r` is `Inductive/Base.rec`, whose descent runs through
   `map`; Agda cannot see into it, hence the pragma.  `Guard` cannot rescue
   it either: its `⊗e` clause quantifies over *all* splittings of the input,
   including the empty one, so it demands `m < m`.

   The missing hypothesis is that the head of a cons really consumes.  That
   is `PayR`'s shape exactly -- it receives the head's inhabitant before it
   owes the order fact -- so non-nullability is all that has to be supplied,
   and the recursion is `löbG`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.KleeneStar.Guarded
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Suffix.Base Alphabet isSetAlphabet
open import Theory.Instances.Monoid.GuardedSplit MonEqns Alphabet (λ _ → tt)
  listPresentation
open import Theory.Type.HLevels MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Inductive.HLevels MonEqns Alphabet (λ _ → tt)
  listPresentation

private variable ℓA ℓB : Level

-- What a cons owes: its head, being inhabited, puts the tail strictly below.
-- This is `PayR` with the `Löb` left implicit, i.e. non-nullability.
NonNull : TheoryTy ℓA tt → Type _
NonNull A = (m : String) (ms : interpIn _⊙_ ↓M) → op _⊙_ ms Eq.≡ m
  → A (ms zero) → ms (suc zero) ◂ m

module _ {A : TheoryTy ℓA tt} (B : TheorySet ℓB tt) (nn : NonNull A) where
  private
    -- the family being fixed: the fold itself, as an internal function
    Fam : TheorySet _ tt
    Fam = (A * ⇒ ty B) , isSet⇒ (isSetTy B)

    module GB = Guarded▷ (λ _ → ty Fam) (λ _ → isSetTy Fam)

    pay : PayR GB.suffixLöb {X = A}
    pay = nn

    unroll↑ : A * ⊢ (A ⊗ (A *)) ⊕ εTy
    unroll↑ = ⊕-elim inl (inr ∘⊢ lowerTy) ∘⊢ unroll*

  module _ (nil : εTy ⊢ ty B) (cons : A ⊗ ty B ⊢ ty B) where
    private
      -- the delayed fold reaches the tail because the head was paid for
      step : (A ⊗ (A *)) & GB.▷ tt ⊢ ty B
      step = cons ∘⊢ (id⊢ ,⊗ (⇒-app ∘⊢ &-swap)) ∘⊢ ▷⊛r GB.suffixLöb pay

      body : GB.▷ tt & (A *) ⊢ ty B
      body = ⊕-elim& (step ∘⊢ &-swap) (nil ∘⊢ π₂) ∘⊢ (id& unroll↑)

    -- ...and Löb closes it.  One combinator, no pragma.
    fold*g : A * ⊢ ty B
    fold*g = ⇒-app ∘⊢ ((GB.löb (λ _ → ⇒-intro body) tt ∘⊢ ⊤Ty-intro) ,& id⊢)
