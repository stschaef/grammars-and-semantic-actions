{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
-- Backreferencing regexes, run.  Every case is `decide-b` on a written
-- `REB`, exactly as `Regex.Tests` is `decide-r` on a written `RE`.
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Backreference.RegexTests where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Maybe as M

data L : Type ℓ-zero where a b : L

_≟L_ : (x y : L) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
a ≟L a = Sum.inl Eq.refl
b ≟L b = Sum.inl Eq.refl
a ≟L b = Sum.inr λ ()
b ≟L a = Sum.inr λ ()

open import Theory.Instances.Monoid.Backreference.Regex L _≟L_ (ℓ-suc ℓ-zero)

ℓr : Level
ℓr = ℓ-suc ℓ-zero

matches : ∀ {ν} (r : REB 0 ν) → String → M.Maybe Unit
matches r = observe (decide-b r ℓr) (semact-dec (semact-pure tt))

-- `(ab)\1`

abab : REB 0 notNullable
abab = grpr (⟨ a ⟩r ⊗r ⟨ b ⟩r) (brefr zero)

_ : matches abab (a ∷ b ∷ a ∷ b ∷ []) ≡ M.just tt
_ = refl

_ : matches abab (a ∷ b ∷ b ∷ a ∷ []) ≡ M.nothing
_ = refl

_ : matches abab (a ∷ b ∷ []) ≡ M.nothing
_ = refl

-- `(a|b)\1` -- the group varies, so the reference is doing work

alt : REB 0 notNullable
alt = grpr (⟨ a ⟩r ⊕r ⟨ b ⟩r) (brefr zero)

_ : matches alt (a ∷ a ∷ []) ≡ M.just tt
_ = refl

_ : matches alt (b ∷ b ∷ []) ≡ M.just tt
_ = refl

_ : matches alt (a ∷ b ∷ []) ≡ M.nothing
_ = refl

_ : matches alt (b ∷ a ∷ []) ≡ M.nothing
_ = refl

-- `(a)(b)\1\2` -- two groups; `brefr zero` is the innermost

two-groups : REB 0 notNullable
two-groups = grpr ⟨ a ⟩r (grpr ⟨ b ⟩r (brefr (suc zero) ⊗r brefr zero))

_ : matches two-groups (a ∷ b ∷ a ∷ b ∷ []) ≡ M.just tt
_ = refl

_ : matches two-groups (a ∷ b ∷ b ∷ a ∷ []) ≡ M.nothing
_ = refl

-- `((a)b)\1` -- a group inside a group's body, which is what `seqDᴰ` is for

nested : REB 0 notNullable
nested = grpr (grpr ⟨ a ⟩r ⟨ b ⟩r) (brefr zero)

_ : matches nested (a ∷ b ∷ a ∷ b ∷ []) ≡ M.just tt
_ = refl

_ : matches nested (a ∷ a ∷ b ∷ b ∷ []) ≡ M.nothing
_ = refl

-- `((a|b)*)\1` -- the copy language `{ww}`, which is not context free

copyRE : REB 0 nullable
copyRE = grpr ((⟨ a ⟩r ⊕r ⟨ b ⟩r) *r) (brefr zero)

_ : matches copyRE [] ≡ M.just tt
_ = refl

_ : matches copyRE (a ∷ a ∷ []) ≡ M.just tt
_ = refl

_ : matches copyRE (a ∷ b ∷ a ∷ b ∷ []) ≡ M.just tt
_ = refl

_ : matches copyRE (a ∷ b ∷ b ∷ a ∷ []) ≡ M.nothing
_ = refl

_ : matches copyRE (a ∷ b ∷ a ∷ []) ≡ M.nothing
_ = refl

_ : matches copyRE (a ∷ b ∷ a ∷ a ∷ b ∷ a ∷ []) ≡ M.just tt
_ = refl

_ : matches copyRE (a ∷ b ∷ b ∷ a ∷ a ∷ b ∷ b ∷ a ∷ []) ≡ M.just tt
_ = refl

_ : matches copyRE (a ∷ b ∷ b ∷ a ∷ a ∷ b ∷ a ∷ b ∷ []) ≡ M.nothing
_ = refl

_ : matches copyRE
      (a ∷ b ∷ b ∷ a ∷ a ∷ b ∷ a ∷ b ∷ a ∷ b ∷ b ∷ a ∷ a ∷ b ∷ a ∷ b ∷ [])
      ≡ M.just tt
_ = refl
