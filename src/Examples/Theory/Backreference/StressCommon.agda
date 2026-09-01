{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
-- Shared setup for the stress cases.  Each case module asserts exactly one
-- equation, so its wall time minus `Base0`.s is the cost of that decision.
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Examples.Theory.Backreference.StressCommon where

open import Cubical.Data.List using (List ; [] ; _∷_) public
open import Cubical.Data.FinData using (Fin ; zero ; suc) public
open import Cubical.Data.Nat using (ℕ) public
import Cubical.Data.Nat as N
open import Cubical.Data.Unit using (Unit ; tt) public
import Cubical.Data.Maybe as M

data L : Type ℓ-zero where a b : L

_≟L_ : (x y : L) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
a ≟L a = Sum.inl Eq.refl
b ≟L b = Sum.inl Eq.refl
a ≟L b = Sum.inr λ ()
b ≟L a = Sum.inr λ ()

open import Theory.Instances.Monoid.Backreference.Regex L _≟L_ (ℓ-suc ℓ-zero)
  public

ℓr : Level
ℓr = ℓ-suc ℓ-zero

matches : ∀ {ν} (r : REB 0 ν) → String → M.Maybe Unit
matches r = observe (decide-b r ℓr) (semact-dec (semact-pure tt))

-- `((a|b)*)\1` : the copy language {ww}
copyRE : REB 0 nullable
copyRE = grpr ((⟨ a ⟩r ⊕r ⟨ b ⟩r) *r) (brefr zero)

-- `(a|b)*` : the same star with no backreference -- the control
starRE : REB 0 nullable
starRE = (⟨ a ⟩r ⊕r ⟨ b ⟩r) *r

-- `((a|aa)*)\1` : an ambiguous group, where the alternation cannot commit
ambigRE : REB 0 nullable
ambigRE = grpr ((⟨ a ⟩r ⊕r (⟨ a ⟩r ⊗r ⟨ a ⟩r)) *r) (brefr zero)
twiceRE : REB 0 notNullable
twiceRE = grpr (⟨ a ⟩r ⊕r ⟨ b ⟩r) (brefr zero ⊗r brefr zero)

-- a literal run of `k+1` a's
repA : ∀ {n} → ℕ → REB n notNullable
repA N.zero = ⟨ a ⟩r
repA (N.suc j) = ⟨ a ⟩r ⊗r repA j

-- `(a^{k+1})\1` : a long *literal* group, so the reference is long
litbackRE : ℕ → REB 0 notNullable
litbackRE j = grpr (repA j) (brefr zero)

-- `k`-deep left-nested capture groups, total yield `a^{k+1}`
nestBody : ∀ {n} → ℕ → REB n notNullable
nestBody N.zero = ⟨ a ⟩r
nestBody (N.suc j) = grpr (nestBody j) ⟨ a ⟩r

-- ...referenced from outside: stresses `seqDᴰ` at depth
deepRE : ℕ → REB 0 notNullable
deepRE j = grpr (nestBody j) (brefr zero)
