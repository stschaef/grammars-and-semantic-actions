{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Predictive choice: alternation indexed by a lookahead cover.

   `_<|>_` decides every branch and combines the decisions.  Committing to
   one instead means *refuting* the others, and a cover refutes them
   generically: `total` names the class of the word, `disjoint` kills every
   other class.  So the separation argument is not a per-grammar
   certificate -- it is the cover's two laws, applied once here.

   What a branch owes is `lead`: whatever follows it, the word is in the
   class it claims.  A branch that leads with a terminal pays it by
   weakening (`leadTok`); a class with no branch pays it vacuously
   (`leadNone`); a branch that may match the empty word cannot pay it at
   all, because the class would then be the continuation's to name.  That
   is exactly the nullability side condition, and it shows up as an
   unwritable argument rather than as a wrong parser. -}
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
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)

open import Theory.Instances.Monoid.Combinator.Decidable.Base Alphabet _≟_ ℓ public
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⊗⊕ᴰ-distL ; &⊕ᴰ-distR)

private variable ℓD ℓY ℓΛ : Level

module Predictive
  {Y : Type ℓY}
  (_≟Y_ : (y y' : Y) → (y Eq.≡ y') Sum.⊎ ((y Eq.≡ y') → Empty.⊥))
  (Λ : Y → TheoryTy ℓΛ tt) (cov : Cover Y Λ)
  (C : Y → TheorySet ℓG tt)
  (lead : (y : Y) → ty (C y) ⊗ ⊤Ty ⊢ Λ y)
  where

  isSetY : isSet Y
  isSetY = Discrete→isSet λ y y' → Sum.rec
    (λ p → yes (Eq.eqToPath p)) (λ ¬p → no λ p → ¬p (Eq.pathToEq p)) (y ≟Y y')
    where open import Cubical.Relation.Nullary.Base using (yes ; no)

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
          branch y' = onSameClass (y' ≟Y y)
            where
            onSameClass : (y' Eq.≡ y) Sum.⊎ ((y' Eq.≡ y) → Empty.⊥)
               → Ctx & (ty (C y') ⊗ ty K) ⊢ ⊥Ty
            onSameClass (Sum.inl Eq.refl) = ⇒-app ∘⊢ ((π₂ ∘⊢ π₁) ,& π₂)
            onSameClass (Sum.inr ne) = elsewhere y y' ne ∘⊢ ((π₁ ∘⊢ π₁) ,& π₂)

    -- `total` names the class; the class decides.
    commit : ty (&ᴰSet Dec·) ⊢ DecTy (ty Alt ⊗ ty K)
    commit = ⊕ᴰ-elim atClass ∘⊢ &⊕ᴰ-distR ∘⊢ (id⊢ ,& (cov .total ∘⊢ ⊤Ty-intro))

  -- Choice with no separation argument: the branches are indexed by the
  -- cover, so at each point exactly one of them is demanded.
  choose : {a c : ParserTag} {D : TheoryTy ℓD tt}
    → ((y : Y) → D ⊢ Parser ℓG a c (C y)) → D ⊢ Parser ℓG a c Alt
  choose p = mkP λ K →
    ▷map (commit K) ∘⊢ ▷laxᴰ (λ y → DecSet (C y ⊗Set K))
    ∘⊢ (&ᴰ-intro λ y → pAt (p y) K)

-- Width 1: the cover of `Lookahead/Base`, and the two ways to pay `lead`

Λ-cover : Cover M₁ Λ₁
Λ-cover .disjoint = Λ-disjoint
Λ-cover .total = Λ-total

-- a bare literal *is* its class, on the nose
leadLit : (c : Alphabet) → ty (litSet c) ⊗ ⊤Ty ⊢ Λ₁ (tk c)
leadLit c = id⊢

leadTok : (c : Alphabet) (X : TheorySet ℓG tt)
  → ty (litSet c ⊗Set X) ⊗ ⊤Ty ⊢ Λ₁ (tk c)
leadTok c X = (id⊢ ,⊗ ⊤Ty-intro) ∘⊢ ⊗-assoc

⊥Set↑ : TheorySet ℓG tt
⊥Set↑ = LiftTheoryTy ℓG ⊥Ty , isSetLiftTheoryTy isSet⊥Ty

leadNone : (y : M₁) → ty ⊥Set↑ ⊗ ⊤Ty ⊢ Λ₁ y
leadNone y = ⊥Ty-elim ∘⊢ ⊗⊥-annihL ∘⊢ (lowerTy ,⊗ id⊢)

noBranch : {a c : ParserTag} {D : TheoryTy ℓD tt} → D ⊢ Parser ℓG a c ⊥Set↑
noBranch = mapP liftTy lowerTy ∘⊢ fail
