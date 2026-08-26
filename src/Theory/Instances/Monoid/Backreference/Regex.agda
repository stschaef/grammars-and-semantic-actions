{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Regular expressions with capture groups and backreferences.

   `REB n` is a regex in the scope of `n` captures.  Nullability is an index
   as in `Regex.Base`, and the scope is a second index: a group is a
   *binder*, so `grpr r kont` is "(r) followed by k", with `k` able to name
   what `r` matched.  Captures are de Bruijn indices, so `brefr zero` is the
   innermost enclosing group.

   `Nullability` and the `RE` constructors are copied from `Regex.Base`
   rather than imported, so that this file and the regex parser stay
   independent.  `satr` is the one constructor not carried over: its yield
   is a character but not a *determined* one, so it does not collapse the
   indexed continuation the way `⟨_⟩r` does.

   A backreference is nullable, because the capture may be the empty string
   -- which is what stops `(\1)*` from being written. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Backreference.Regex
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)

open import Theory.Instances.Monoid.Backreference.Parser Alphabet _≟_ ℓ public

private variable n : ℕ

------------------------------------------------------------------------
-- Nullability (copied from `Regex.Base`)

data Nullability : Type ℓ-zero where
  nullable notNullable : Nullability

ν≢ν̸ : nullable ≡ notNullable → Empty.⊥
ν≢ν̸ p = subst Discern p tt
  where
  Discern : Nullability → Type ℓ-zero
  Discern nullable = Unit
  Discern notNullable = Empty.⊥

_·ν_ : Nullability → Nullability → Nullability
notNullable ·ν _ = notNullable
nullable ·ν y = y

_+ν_ : Nullability → Nullability → Nullability
nullable +ν _ = nullable
notNullable +ν y = y

------------------------------------------------------------------------
-- The syntax

data REB : ℕ → Nullability → Type ℓAlph where
  εr   : REB n nullable
  ⊥r   : REB n notNullable
  ⟨_⟩r : Alphabet → REB n notNullable
  _⊗r_ : ∀ {ν ν'} → REB n ν → REB n ν' → REB n (ν ·ν ν')
  _⊕r_ : ∀ {ν ν'} → REB n ν → REB n ν' → REB n (ν +ν ν')
  _*r  : REB n notNullable → REB n nullable
  -- a capture group, scoping over everything that follows it
  grpr : ∀ {ν ν'} → REB n ν → REB (suc n) ν' → REB n (ν ·ν ν')
  -- ...and a reference back to one
  brefr : Fin n → REB n nullable

infixr 20 _⊗r_
infixr 19 _⊕r_
infix 30 _*r
infix 30 ⟨_⟩r

_+r : REB n notNullable → REB n notNullable
r +r = r ⊗r (r *r)

infix 30 _+r

-- what the enclosing groups matched
Env : ℕ → Type ℓM
Env n = Fin n → String

ext : Env n → String → Env (suc n)
ext γ l zero = l
ext γ l (suc i) = γ i

lv : ∀ {ν} → REB n ν → Level
lv εr = ℓM
lv ⊥r = ℓ-zero
lv ⟨ c ⟩r = ℓM
lv (r ⊗r r') = ℓ-max ℓAlph (ℓ-max (lv r) (lv r'))
lv (r ⊕r r') = ℓ-max (lv r) (lv r')
lv (r *r) = ℓF (lv r)
lv (grpr r kont) = ℓ-max ℓAlph (ℓ-max (lv r) (lv kont))
lv (brefr i) = ℓM

------------------------------------------------------------------------
-- Semantics: a regex in scope `n` denotes a family of grammars

⟦_⟧ : ∀ {ν} (r : REB n ν) → Env n → TheorySet (lv r) tt
⟦ εr ⟧ γ = εSet
⟦ ⊥r ⟧ γ = ⊥Set
⟦ ⟨ c ⟩r ⟧ γ = litSet c
⟦ r ⊗r r' ⟧ γ = ⟦ r ⟧ γ ⊗Set ⟦ r' ⟧ γ
⟦ r ⊕r r' ⟧ γ = ⟦ r ⟧ γ ⊕Set ⟦ r' ⟧ γ
⟦ r *r ⟧ γ = StarSet (⟦ r ⟧ γ)
⟦ grpr r kont ⟧ γ = ⊗ᴰSet (⟦ r ⟧ γ) (λ l → ⟦ kont ⟧ (ext γ l))
⟦ brefr i ⟧ γ = ⌈ γ i ⌉Set

------------------------------------------------------------------------
-- The parser.  Only the publishing form is written: `toParser` gives the
-- ordinary one back for free, so there is no second copy of this recursion.

parseD  : ∀ {ν} (r : REB n ν) (γ : Env n) (ℓK : Level)
        → ⊤Ty ⊢ ParserD (ℓ-max ℓM ℓK) ⟨□⟩ ⟨□⟩ (⟦ r ⟧ γ)
parseD▷ : ∀ {ν} (r : REB n ν) (γ : Env n) (ℓK : Level) → ν ≡ notNullable
        → ⊤Ty ⊢ ParserD (ℓ-max ℓM ℓK) ⟨▷⟩ ⟨□⟩ (⟦ r ⟧ γ)

parseD εr γ ℓK = nilD
parseD ⊥r γ ℓK = failD
parseD ⟨ c ⟩r γ ℓK = pmoreD ∘⊢ tokD c
parseD (r ⊗r r') γ ℓK =
  seqDD (⟦ r' ⟧ γ) (parseD r γ (ℓ⊗ (lv r') ℓK)) (parseD r' γ ℓK)
parseD (r ⊕r r') γ ℓK = parseD r γ ℓK <|>D parseD r' γ ℓK
parseD (r *r) γ ℓK =
  manyD ℓK (⟦ r ⟧ γ) (parseD▷ r γ (ℓ⊗ (ℓF (lv r)) ℓK) refl)
parseD (grpr r kont) γ ℓK =
  seqDᴰ (λ l → ⟦ kont ⟧ (ext γ l))
    (parseD r γ (ℓ⊗ (lv kont) ℓK))
    (λ l → parseD kont (ext γ l) ℓK)
parseD (brefr i) γ ℓK = strPD (γ i)

parseD▷ εr γ ℓK p = Empty.rec (ν≢ν̸ p)
parseD▷ ⊥r γ ℓK p = failD
parseD▷ ⟨ c ⟩r γ ℓK p = tokD c
parseD▷ (_⊗r_ {ν = notNullable} {ν' = ν'} r r') γ ℓK p =
  seqDD (⟦ r' ⟧ γ) (parseD▷ r γ (ℓ⊗ (lv r') ℓK) refl) (boxD (parseD r' γ ℓK))
parseD▷ (_⊗r_ {ν = nullable} {ν' = notNullable} r r') γ ℓK p =
  seqDD (⟦ r' ⟧ γ) (parseD r γ (ℓ⊗ (lv r') ℓK)) (parseD▷ r' γ ℓK refl)
parseD▷ (_⊗r_ {ν = nullable} {ν' = nullable} r r') γ ℓK p = Empty.rec (ν≢ν̸ p)
parseD▷ (_⊕r_ {ν = notNullable} {ν' = notNullable} r r') γ ℓK p =
  parseD▷ r γ ℓK refl <|>D parseD▷ r' γ ℓK refl
parseD▷ (_⊕r_ {ν = notNullable} {ν' = nullable} r r') γ ℓK p = Empty.rec (ν≢ν̸ p)
parseD▷ (_⊕r_ {ν = nullable} {ν' = ν'} r r') γ ℓK p = Empty.rec (ν≢ν̸ p)
parseD▷ (r *r) γ ℓK p = Empty.rec (ν≢ν̸ p)
parseD▷ (grpr {ν = notNullable} {ν' = ν'} r kont) γ ℓK p =
  seqDᴰ (λ l → ⟦ kont ⟧ (ext γ l))
    (parseD▷ r γ (ℓ⊗ (lv kont) ℓK) refl)
    (λ l → boxD (parseD kont (ext γ l) ℓK))
parseD▷ (grpr {ν = nullable} {ν' = notNullable} r kont) γ ℓK p =
  seqDᴰ (λ l → ⟦ kont ⟧ (ext γ l))
    (parseD r γ (ℓ⊗ (lv kont) ℓK))
    (λ l → parseD▷ kont (ext γ l) ℓK refl)
parseD▷ (grpr {ν = nullable} {ν' = nullable} r kont) γ ℓK p = Empty.rec (ν≢ν̸ p)
parseD▷ (brefr i) γ ℓK p = Empty.rec (ν≢ν̸ p)

parse : ∀ {ν} (r : REB n ν) (γ : Env n) (ℓK : Level)
      → ⊤Ty ⊢ Parser (ℓ-max ℓM ℓK) ⟨□⟩ ⟨□⟩ (⟦ r ⟧ γ)
parse r γ ℓK = toParser (parseD r γ ℓK)

-- A closed regex decides its own language.
decide-b : ∀ {ν} (r : REB 0 ν) (ℓK : Level) → Decidable (ty (⟦ r ⟧ λ ()))
decide-b r ℓK = runP ℓK (parse r (λ ()) ℓK)
