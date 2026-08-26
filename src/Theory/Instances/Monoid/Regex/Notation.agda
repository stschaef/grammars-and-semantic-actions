{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The surface syntax of regular expressions.

   Everything here is derived from the six formers in `Regex.Base`; nothing
   adds parsing power.  What it adds is that the nullability index stays
   definitional: `εr ⊕r r` reduces (`nullable +ν n = nullable`) where `r ⊕r εr`
   does not, so the disjuncts are ordered for the type checker rather than
   for the reader. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Regex.Notation
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Cubical.Data.Bool using (Bool ; true ; false ; _and_ ; _or_ ; not)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)

open import Theory.Instances.Monoid.Regex.Base Alphabet _≟_ ℓ public

private
  eqb : Alphabet → Alphabet → Bool
  eqb x y = Sum.rec (λ _ → true) (λ _ → false) (x ≟ y)

  elemb : Alphabet → List Alphabet → Bool
  elemb c [] = false
  elemb c (d ∷ ds) = eqb c d or elemb c ds

------------------------------------------------------------------------
-- Character classes.  `satr` makes all of these one-liners, and the
-- complement is no harder than the set -- which is the point of taking a
-- predicate rather than a list of disjuncts.

-- `[abc]`
oneOfr : List Alphabet → RE notNullable
oneOfr cs = satr λ c → elemb c cs

-- `[^abc]`
noneOfr : List Alphabet → RE notNullable
noneOfr cs = satr λ c → not (elemb c cs)

------------------------------------------------------------------------
-- Postfix repetition.  The disjunct order is what keeps the index
-- reducing: `nullable +ν n` computes, `n +ν nullable` does not.

-- `r?`
_?r : ∀ {n} → RE n → RE nullable
r ?r = εr ⊕r r

-- `r|s|…` over a list of rules -- `⊥r` is the unit, and
-- `notNullable +ν notNullable` computes, which is why this is stated at
-- the non-nullable index
anyOfr : List (RE notNullable) → RE notNullable
anyOfr [] = ⊥r
anyOfr (r ∷ rs) = r ⊕r anyOfr rs

infix 30 _?r

------------------------------------------------------------------------
-- Literal words.  The index is the emptiness of the list, which `_and_`
-- computes on the left: `notNullable ·ν n = notNullable`.

nullb : List Alphabet → Nullability
nullb [] = nullable
nullb (_ ∷ _) = notNullable

-- `"abc"`
strr : (w : List Alphabet) → RE (nullb w)
strr [] = εr
strr (c ∷ w) = ⟨ c ⟩r ⊗r strr w

------------------------------------------------------------------------
-- Counted repetition.  `r{n}`, `r{,n}`, `r{n,m}`.  All are on a
-- non-nullable body, which is what the star already demands.

zerob : ℕ → Nullability
zerob zero = nullable
zerob (suc _) = notNullable

-- `r{n}`
repr : (n : ℕ) → RE notNullable → RE (zerob n)
repr zero r = εr
repr (suc n) r = r ⊗r repr n r

-- `r{,n}` -- at most n
atMostr : (n : ℕ) → RE notNullable → RE nullable
atMostr zero r = εr
atMostr (suc n) r = εr ⊕r (r ⊗r atMostr n r)

-- `r{n,m}` -- n copies, then up to  more
betweenr : (n extra : ℕ) → RE notNullable → RE (zerob n)
betweenr zero extra r = atMostr extra r
betweenr (suc n) extra r = r ⊗r betweenr n extra r
