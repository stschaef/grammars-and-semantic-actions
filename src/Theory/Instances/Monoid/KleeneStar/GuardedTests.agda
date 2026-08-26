{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `fold*g` computes: the same star fold as `fold*r`, by löb rather than by
   an asserted recursion. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
module Theory.Instances.Monoid.KleeneStar.GuardedTests where
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Maybe as M

data L : Type ℓ-zero where a b : L

_≟L_ : (x y : L) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
a ≟L a = Sum.inl Eq.refl
b ≟L b = Sum.inl Eq.refl
a ≟L b = Sum.inr λ ()
b ≟L a = Sum.inr λ ()

open import Theory.Instances.Monoid.Combinator.Incomplete.Star L _≟L_ (ℓ-suc ℓ-zero)
open import Theory.Instances.Monoid.KleeneStar.Guarded L isSetAlphabet
import Theory.Instances.Monoid.SemanticAction L isSetAlphabet as Act

Count : TheorySet ℓ-zero tt
Count = Act.Δ ℕ , isSet⊕ᴰ isSetℕ (λ _ → isSet⊤Ty)

-- the client states non-nullability internally, and never sees the order
nn : ¬Nullable (literal a)
nn = literal-¬Nullable a

-- the fold, by guarded recursion
len : SemanticAction ((literal a) *) ℕ
len = fold*g Count nn (semact-pure 0) (semact-map suc (semact-⊗ᵣ id⊢))

countAs : String → M.Maybe ℕ
countAs = observe (runP (ℓ-suc ℓ-zero) (many (ℓ-suc ℓ-zero) (litSet a) (tok a)))
                  (semact-Maybe len)

-- ...and it computes
_ : countAs [] ≡ M.just 0
_ = refl

_ : countAs (a ∷ a ∷ a ∷ []) ≡ M.just 3
_ = refl

_ : countAs (a ∷ a ∷ a ∷ a ∷ a ∷ []) ≡ M.just 5
_ = refl

_ : countAs (b ∷ []) ≡ M.nothing
_ = refl
