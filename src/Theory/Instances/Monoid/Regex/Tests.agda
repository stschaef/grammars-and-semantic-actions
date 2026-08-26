{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
-- The regex parser runs: every case is `decide-r` on a written regex.
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Regex.Tests where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Maybe as M

data L : Type ℓ-zero where a b : L

_≟L_ : (x y : L) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
a ≟L a = Sum.inl Eq.refl
b ≟L b = Sum.inl Eq.refl
a ≟L b = Sum.inr λ ()
b ≟L a = Sum.inr λ ()

open import Theory.Instances.Monoid.Regex.Base L _≟L_ (ℓ-suc ℓ-zero)

ℓr : Level
ℓr = ℓ-suc ℓ-zero

matches : ∀ {n} (r : RE n) → String → M.Maybe Unit
matches r = observe (decide-r r ℓr) (semact-dec (semact-pure tt))

------------------------------------------------------------------------
-- `a b`

ab : RE false
ab = ⟨ a ⟩r ⊗r ⟨ b ⟩r

_ : matches ab (a ∷ b ∷ []) ≡ M.just tt
_ = refl

_ : matches ab (a ∷ []) ≡ M.nothing
_ = refl

_ : matches ab (b ∷ a ∷ []) ≡ M.nothing
_ = refl

------------------------------------------------------------------------
-- `a *`

as : RE true
as = ⟨ a ⟩r *r

_ : matches as [] ≡ M.just tt
_ = refl

_ : matches as (a ∷ a ∷ a ∷ []) ≡ M.just tt
_ = refl

_ : matches as (a ∷ b ∷ []) ≡ M.nothing
_ = refl

------------------------------------------------------------------------
-- `(a | b) *` -- alternation under a star

abs : RE true
abs = (⟨ a ⟩r ⊕r ⟨ b ⟩r) *r

_ : matches abs [] ≡ M.just tt
_ = refl

_ : matches abs (a ∷ b ∷ a ∷ b ∷ []) ≡ M.just tt
_ = refl

------------------------------------------------------------------------
-- `a b *` -- a non-nullable head before a nullable tail, the case the
-- two-tag fold exists for

abs' : RE false
abs' = ⟨ a ⟩r ⊗r (⟨ b ⟩r *r)

_ : matches abs' (a ∷ []) ≡ M.just tt
_ = refl

_ : matches abs' (a ∷ b ∷ b ∷ []) ≡ M.just tt
_ = refl

_ : matches abs' [] ≡ M.nothing
_ = refl

------------------------------------------------------------------------
-- `. +` -- one or more of anything

anyPlus : RE false
anyPlus = anyr +r

_ : matches anyPlus (a ∷ b ∷ []) ≡ M.just tt
_ = refl

_ : matches anyPlus [] ≡ M.nothing
_ = refl
