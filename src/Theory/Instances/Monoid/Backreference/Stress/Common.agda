{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
-- Shared setup for the stress cases: one alphabet, one `matches`, and the
-- patterns under test.
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Backreference.Stress.Common where

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

-- `(a)(b)(a)(b)\1\2\3\4`
fourRE : REB 0 notNullable
fourRE =
  grpr ⟨ a ⟩r (grpr ⟨ b ⟩r (grpr ⟨ a ⟩r (grpr ⟨ b ⟩r
    (brefr (suc (suc (suc zero))) ⊗r brefr (suc (suc zero))
     ⊗r brefr (suc zero) ⊗r brefr zero))))

-- `(a|b)\1\1` : one capture, referenced twice
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

-- referenced from outside: stresses `seqDᴰ` at depth
deepRE : ℕ → REB 0 notNullable
deepRE j = grpr (nestBody j) (brefr zero)

-- `(a|aa)*` : the ambiguous star with NO backreference -- the control that
-- says where the exponential actually comes from
ambigStarRE : REB 0 nullable
ambigStarRE = (⟨ a ⟩r ⊕r (⟨ a ⟩r ⊗r ⟨ a ⟩r)) *r

-- `(a|b)* (ab) \1 (a|b)*` : find a doubled two-character token anywhere in
-- the input.  A short, bounded group -- what a real backreference looks
-- like -- rather than the unanchored star group of `copyRE`.
searchRE : REB 0 notNullable
searchRE =
  ((⟨ a ⟩r ⊕r ⟨ b ⟩r) *r)
  ⊗r grpr (⟨ a ⟩r ⊗r ⟨ b ⟩r)
       (brefr zero ⊗r ((⟨ a ⟩r ⊕r ⟨ b ⟩r) *r))

-- Controls with the *same shape* as the backreferencing patterns but no
-- backreference at all, to say what the reference actually costs.
ctlTailRE : REB 0 notNullable          -- (a|b)* ab          one star
ctlTailRE = ((⟨ a ⟩r ⊕r ⟨ b ⟩r) *r) ⊗r (⟨ a ⟩r ⊗r ⟨ b ⟩r)

ctlMidRE : REB 0 notNullable           -- (a|b)* ab (a|b)*   two stars
ctlMidRE =
  ((⟨ a ⟩r ⊕r ⟨ b ⟩r) *r) ⊗r (⟨ a ⟩r ⊗r ⟨ b ⟩r) ⊗r ((⟨ a ⟩r ⊕r ⟨ b ⟩r) *r)

ctlTwoStarRE : REB 0 nullable          -- (a|b)*(a|b)*       copyRE minus \1
ctlTwoStarRE = ((⟨ a ⟩r ⊕r ⟨ b ⟩r) *r) ⊗r ((⟨ a ⟩r ⊕r ⟨ b ⟩r) *r)

-- `(a|b)* (ab) ab (a|b)*` : a *capture group* whose continuation does not
-- mention the capture -- same language as `searchRE`, same `grpr`/`seqDᴰ`
-- machinery, but the reference is replaced by the literal it would match.
-- This separates the cost of the group from the cost of the reference.
ctlGrpRE : REB 0 notNullable
ctlGrpRE =
  ((⟨ a ⟩r ⊕r ⟨ b ⟩r) *r)
  ⊗r grpr (⟨ a ⟩r ⊗r ⟨ b ⟩r)
       ((⟨ a ⟩r ⊗r ⟨ b ⟩r) ⊗r ((⟨ a ⟩r ⊕r ⟨ b ⟩r) *r))

-- `(a|b)* (ab) ab` : a group whose continuation has no trailing star.
-- If `grpr` were inherently quadratic this would be too.
ctlGrpTailRE : REB 0 notNullable
ctlGrpTailRE =
  ((⟨ a ⟩r ⊕r ⟨ b ⟩r) *r) ⊗r grpr (⟨ a ⟩r ⊗r ⟨ b ⟩r) (⟨ a ⟩r ⊗r ⟨ b ⟩r)

-- the same with the reference, still no trailing star
ctlGrpTailRefRE : REB 0 notNullable
ctlGrpTailRefRE =
  ((⟨ a ⟩r ⊕r ⟨ b ⟩r) *r) ⊗r grpr (⟨ a ⟩r ⊗r ⟨ b ⟩r) (brefr zero)
