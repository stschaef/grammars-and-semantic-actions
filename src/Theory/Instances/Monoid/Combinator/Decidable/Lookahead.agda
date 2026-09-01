{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Predictive choice: alternation indexed by a lookahead cover.  Committing
   refutes the other branches by the cover's two laws alone; a nullable branch
   cannot pay `lead`, so the side condition is an unwritable argument. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Decidable.Lookahead
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Combinator.Decidable.Base Alphabet _≟_ ℓ public
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⊗⊕ᴰ-distL)

private variable ℓD ℓY ℓΛ : Level

module Predictive
  {Y : Type ℓY}
  (_≟Y_ : (y y' : Y) → (y Eq.≡ y') Sum.⊎ ((y Eq.≡ y') → Empty.⊥))
  (Λ : Y → TheoryTy ℓΛ tt) (cov : Cover Y Λ)
  (C : Y → TheorySet ℓG tt)
  (lead : (y : Y) → ty (C y) ⊗ ⊤Ty ⊢ Λ y)
  where

  isSetY : isSet Y
  isSetY = DiscreteEq→isSet _≟Y_

  Alt : TheorySet (ℓ-max ℓY ℓG) tt
  Alt = ⊕ᴰSet isSetY C

  module _ (K : TheorySet ℓG tt) where
    private
      Dec· : Y → TheorySet ℓG tt
      Dec· y = DecSet (C y ⊗Set K)

      -- a branch other than the observed one is refuted by the cover alone
      elsewhere : (y y' : Y) → (y' Eq.≡ y → Empty.⊥)
        → Λ y & (ty (C y') ⊗ ty K) ⊢ ⊥Ty
      elsewhere y y' ne =
        cov .disjoint y y' (λ e → ne (Eq.sym e))
        ∘⊢ (id⊢ ,&p (lead y' ∘⊢ (id⊢ ,⊗ ⊤Ty-intro)))

      -- ...so at the observed class, that branch's decision is the whole one
      atClass : (y : Y)
        → ty (&ᴰSet Dec·) & Λ y ⊢ DecTy (ty Alt ⊗ ty K)
      atClass y = ⊕-elim& yes' no' ∘⊢ (π₂ ,& (π y ∘⊢ π₁))
        where
        yes' : Λ y & (ty (C y) ⊗ ty K) ⊢ DecTy (ty Alt ⊗ ty K)
        yes' = dec-yes ∘⊢ (σ⊕ y ,⊗ id⊢) ∘⊢ π₂

        no' : Λ y & ¬Ty (ty (C y) ⊗ ty K) ⊢ DecTy (ty Alt ⊗ ty K)
        no' = dec-no ∘⊢ ⇒-intro
          (⊕ᴰ-elim branch ∘⊢ &⊕ᴰ-distR ∘⊢ (id⊢ ,&p ⊗⊕ᴰ-distL))
          where
          Ctx : TheoryTy _ tt
          Ctx = Λ y & ¬Ty (ty (C y) ⊗ ty K)

          branch : (y' : Y) → Ctx & (ty (C y') ⊗ ty K) ⊢ ⊥Ty
          branch y' = go (y' ≟Y y)
            where
            go : (y' Eq.≡ y) Sum.⊎ ((y' Eq.≡ y) → Empty.⊥)
               → Ctx & (ty (C y') ⊗ ty K) ⊢ ⊥Ty
            go (Sum.inl Eq.refl) = ⇒-app ∘⊢ ((π₂ ∘⊢ π₁) ,& π₂)
            go (Sum.inr ne) = elsewhere y y' ne ∘⊢ ((π₁ ∘⊢ π₁) ,& π₂)

    -- the whole use of the cover: `total` names the class, the class decides
    commit : ty (&ᴰSet Dec·) ⊢ DecTy (ty Alt ⊗ ty K)
    commit = ⊕ᴰ-elim atClass ∘⊢ &⊕ᴰ-distR ∘⊢ (id⊢ ,& (cov .total ∘⊢ ⊤Ty-intro))

  -- no separation argument: at each point exactly one branch is demanded
  choose : {a c : ParserTag} {D : TheoryTy ℓD tt}
    → ((y : Y) → D ⊢ Parser ℓG a c (C y)) → D ⊢ Parser ℓG a c Alt
  choose p = mkP λ K →
    ▷map (commit K) ∘⊢ ▷laxᴰ (λ y → DecSet (C y ⊗Set K))
    ∘⊢ (&ᴰ-intro λ y → pAt (p y) K)

-- Width 1: the cover of `Lookahead/Base`, and the two ways to pay `lead`

Λ-cover : Cover M₁ Λ₁
Λ-cover .disjoint = Λ-disjoint
Λ-cover .total = Λ-total
-- ...and a class with no branch claims it vacuously
⊥Set↑ : TheorySet ℓG tt
⊥Set↑ = LiftTheoryTy ℓG ⊥Ty , isSetLiftTheoryTy isSet⊥Ty

leadNone : (y : M₁) → ty ⊥Set↑ ⊗ ⊤Ty ⊢ Λ₁ y
leadNone y = ⊥Ty-elim ∘⊢ ⊗⊥-annihL ∘⊢ (lowerTy ,⊗ id⊢)
