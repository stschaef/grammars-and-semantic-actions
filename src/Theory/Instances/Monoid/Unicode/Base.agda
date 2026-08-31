{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- Unicode characters as an internal type.

   `String.Unicode` decides character equality through a *postulated* path
   oracle, so `c ≟ d` never reduces to `Eq.refl` and no parser over that
   alphabet computes.  A code point is a number below 0x110000, so 21 bits
   carry one: equality is then structural and reduces.

   The only external step left is `primCharToNat`, which is a genuine
   primitive and does reduce on literals -- so real text still enters. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Unicode.Base where

open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; map)
open import Cubical.Relation.Nullary.DiscreteEq using (DiscreteEq→isSet)
open import Cubical.Relation.Nullary.Base using (yes ; no)
open import Agda.Builtin.Nat using (div-helper ; mod-helper)
import Agda.Builtin.Char as AC
import Agda.Builtin.String as AS

private
  half : ℕ → ℕ
  half n = div-helper 0 1 n 1

  odd : ℕ → Bool
  odd n with mod-helper 0 1 n 1
  ... | zero = false
  ... | suc _ = true

data Bits : ℕ → Type ℓ-zero where
  [] : Bits zero
  _-∷_ : {k : ℕ} → Bool → Bits k → Bits (suc k)

infixr 5 _-∷_

fromNat : (k : ℕ) → ℕ → Bits k
fromNat zero n = []
fromNat (suc k) n = odd n -∷ fromNat k (half n)

-- structural, so it reduces to `Eq.refl` -- the whole point
_≟Bits_ : {k : ℕ} (x y : Bits k) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
[] ≟Bits [] = Sum.inl Eq.refl
(true -∷ x) ≟Bits (true -∷ y) with x ≟Bits y
... | Sum.inl Eq.refl = Sum.inl Eq.refl
... | Sum.inr ne = Sum.inr λ where Eq.refl → ne Eq.refl
(false -∷ x) ≟Bits (false -∷ y) with x ≟Bits y
... | Sum.inl Eq.refl = Sum.inl Eq.refl
... | Sum.inr ne = Sum.inr λ where Eq.refl → ne Eq.refl
(true -∷ x) ≟Bits (false -∷ y) = Sum.inr λ ()
(false -∷ x) ≟Bits (true -∷ y) = Sum.inr λ ()

-- 21 bits span 0 .. 0x10FFFF, which is every code point
UChar : Type ℓ-zero
UChar = Bits 21

_≟U_ : (x y : UChar) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
_≟U_ = _≟Bits_

isSetUChar : isSet UChar
isSetUChar = DiscreteEq→isSet _≟U_

-- Accumulator form, so the recursive call appears once.  Measured: the
-- duplicating form (`toNat bs + toNat bs`) is no slower, so Agda shares
-- the thunk -- this is defensive, not a fix.
toNat : {k : ℕ} → Bits k → ℕ
toNat = go 1
  where
  go : {k : ℕ} → ℕ → Bits k → ℕ
  go w [] = 0
  go w (true -∷ bs) = w + go (w + w) bs
  go w (false -∷ bs) = go (w + w) bs

ch : AC.Char → UChar
ch c = fromNat 21 (AC.primCharToNat c)

-- the code point back out, so a range can be decided by comparison
code : UChar → ℕ
code = toNat

-- text enters the theory here and nowhere else
text : AS.String → List UChar
text s = map ch (AS.primStringToList s)

-- ...and leaves here, which is what lets a test state its result as text
unch : UChar → AC.Char
unch b = AC.primNatToChar (toNat b)

untext : List UChar → AS.String
untext cs = AS.primStringFromList (map unch cs)
