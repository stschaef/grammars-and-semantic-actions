open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit using (tt)

module Theory.Instances.Monoid.RegularExpression
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet

data RegularExpression : Type ℓAlph where
  εr : RegularExpression
  ⊥r : RegularExpression
  _⊗r_ : RegularExpression → RegularExpression → RegularExpression
  ＂_＂r : Alphabet → RegularExpression
  _⊕r_ : RegularExpression → RegularExpression → RegularExpression
  _*r : RegularExpression → RegularExpression

Regex : Type ℓAlph
Regex = RegularExpression

-- The universe of a star rises with its body in the generic inductive
-- construction, so the interpretation carries its level explicitly.
regexLevel : RegularExpression → Level
regexLevel εr = ℓM
regexLevel ⊥r = ℓM
regexLevel (r ⊗r r') = ℓ-max ℓM (ℓ-max (regexLevel r) (regexLevel r'))
regexLevel (＂ _ ＂r) = ℓM
regexLevel (r ⊕r r') = ℓ-max (regexLevel r) (regexLevel r')
regexLevel (r *r) = ℓF (regexLevel r)

RegularExpression→Grammar : (r : RegularExpression) → TheoryTy (regexLevel r) tt
RegularExpression→Grammar εr = εTy
RegularExpression→Grammar ⊥r = ⊥Ty↑ ℓM
RegularExpression→Grammar (r ⊗r r') =
  RegularExpression→Grammar r ⊗ RegularExpression→Grammar r'
RegularExpression→Grammar (＂ c ＂r) = literal c
RegularExpression→Grammar (r ⊕r r') =
  RegularExpression→Grammar r ⊕ RegularExpression→Grammar r'
RegularExpression→Grammar (r *r) = (RegularExpression→Grammar r) *

⟦_⟧r : (r : RegularExpression) → TheoryTy (regexLevel r) tt
⟦_⟧r = RegularExpression→Grammar

infix 30 ＂_＂r
infixr 20 _⊗r_
infixr 20 _⊕r_
infix 30 _*r

_+r : RegularExpression → RegularExpression
r +r = r ⊗r r *r

infix 30 _+r
