{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Surface regex syntax over `Regex.Base`.  Disjunct order keeps the
   nullability index definitional: `εr ⊕r r` reduces, `r ⊕r εr` does not. -}
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
open import Theory.Instances.Monoid.Types Alphabet _≟_ hiding (isSetAlphabet) public
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet public
open import Theory.Instances.Monoid.KleeneStar.Guarded Alphabet isSetAlphabet public

private
  eqb : Alphabet → Alphabet → Bool
  eqb x y = Sum.rec (λ _ → true) (λ _ → false) (x ≟ y)

  elemb : Alphabet → List Alphabet → Bool
  elemb c [] = false
  elemb c (d ∷ ds) = eqb c d or elemb c ds

-- Classes as predicates: the complement is no harder than the set.

-- `[abc]`
oneOfr : List Alphabet → RE notNullable
oneOfr cs = satr λ c → elemb c cs

-- `[^abc]`
noneOfr : List Alphabet → RE notNullable
noneOfr cs = satr λ c → not (elemb c cs)

-- `r?`
_?r : ∀ {n} → RE n → RE nullable
r ?r = εr ⊕r r

-- `r|s|…`; `⊥r` is the unit, and `notNullable +ν notNullable` computes
anyOfr : List (RE notNullable) → RE notNullable
anyOfr [] = ⊥r
anyOfr (r ∷ []) = r                        -- no trailing `⊕r ⊥r` to explore
anyOfr (r ∷ rs@(_ ∷ _)) = r ⊕r anyOfr rs

infix 30 _?r

nullb : List Alphabet → Nullability
nullb [] = nullable
nullb (_ ∷ _) = notNullable

-- `"abc"`
strr : (w : List Alphabet) → RE (nullb w)
strr [] = εr
strr (c ∷ w) = ⟨ c ⟩r ⊗r strr w

-- Counted repetition, on a non-nullable body as the star already demands.

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
