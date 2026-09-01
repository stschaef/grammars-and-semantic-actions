{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- POSIX regular expressions at Unicode: ranges need `UChar`'s `code` ordering.
   A class is a predicate first, so complements are free (`\D` is `satr (not ∘ isDigit)`). -}
open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.Regex.Unicode where

open import Cubical.Data.Bool using (Bool ; true ; false ; _and_ ; _or_ ; not)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Nat using (ℕ)
import Agda.Builtin.Nat as AN
import Agda.Builtin.Char as AC
import Agda.Builtin.String as AS

open import Cubical.Data.Unicode public
open import Theory.Instances.Monoid.Regex.Notation UChar _≟U_ (ℓ-suc ℓ-zero)
  public
open import Theory.Instances.Monoid.Regex.Decide UChar _≟U_ (ℓ-suc ℓ-zero)
  public

private
  _≤ᵇ_ : ℕ → ℕ → Bool
  m ≤ᵇ n = not (AN._<_ n m)

  -- `primCharToNat` already is the code point: no `ch`/`code` round trip
  eqc : AC.Char → UChar → Bool
  eqc d c = AN._==_ (AC.primCharToNat d) (code c)

inRange : AC.Char → AC.Char → UChar → Bool
inRange lo hi c =
  (AC.primCharToNat lo ≤ᵇ code c) and (code c ≤ᵇ AC.primCharToNat hi)

isDigit isUpper isLower isAlpha isAlnum isXDigit : UChar → Bool
isDigit  = inRange '0' '9'
isUpper  = inRange 'A' 'Z'
isLower  = inRange 'a' 'z'
isAlpha  c = isLower c or isUpper c
isAlnum  c = isAlpha c or isDigit c
isXDigit c = isDigit c or inRange 'a' 'f' c or inRange 'A' 'F' c

isBlank isSpace isCntrl isPrint isGraph isPunct isWord : UChar → Bool
isBlank c = eqc ' ' c or eqc '\t' c
isSpace c = isBlank c or eqc '\n' c or eqc '\r' c
          or eqc '\v' c or eqc '\f' c
isCntrl c = inRange '\x00' '\x1F' c or eqc '\x7F' c
isPrint   = inRange '\x20' '\x7E'
isGraph   = inRange '\x21' '\x7E'
isPunct c = isGraph c and not (isAlnum c)
isWord  c = isAlnum c or eqc '_' c

-- `[lo-hi]`
rangeR : AC.Char → AC.Char → RE notNullable
rangeR lo hi = satr (inRange lo hi)

-- `[c]`
charR : AC.Char → RE notNullable
charR c = ⟨ ch c ⟩r

digitR alphaR alnumR upperR lowerR xdigitR : RE notNullable
spaceR blankR punctR cntrlR printR graphR wordR : RE notNullable
digitR  = satr isDigit
alphaR  = satr isAlpha
alnumR  = satr isAlnum
upperR  = satr isUpper
lowerR  = satr isLower
xdigitR = satr isXDigit
spaceR  = satr isSpace
blankR  = satr isBlank
punctR  = satr isPunct
cntrlR  = satr isCntrl
printR  = satr isPrint
graphR  = satr isGraph
wordR   = satr isWord

-- `\D`, `\S`, `\W` -- free, because a class is a predicate
notDigitR notSpaceR notWordR : RE notNullable
notDigitR = satr λ c → not (isDigit c)
notSpaceR = satr λ c → not (isSpace c)
notWordR  = satr λ c → not (isWord c)

-- `.` -- POSIX's dot excludes the newline
dotR : RE notNullable
dotR = satr λ c → not (eqc '\n' c)

-- Bracket expressions: `[abc0-9[:alpha:]]` is a union of items.

data Item : Type ℓ-zero where
  chI    : AC.Char → Item
  rangeI : AC.Char → AC.Char → Item
  classI : (UChar → Bool) → Item

itemHolds : Item → UChar → Bool
itemHolds (chI d) c = eqc d c
itemHolds (rangeI lo hi) c = inRange lo hi c
itemHolds (classI P) c = P c

anyItem : List Item → UChar → Bool
anyItem [] c = false
anyItem (i ∷ is) c = itemHolds i c or anyItem is c

-- `[…]`
bracketR : List Item → RE notNullable
bracketR is = satr (anyItem is)

-- `[^…]`
bracketNotR : List Item → RE notNullable
bracketNotR is = satr λ c → not (anyItem is c)

-- `strU "let"` rather than `strr (ch 'l' ∷ ch 'e' ∷ ch 't' ∷ [])`

strU : (w : AS.String) → RE (nullb (text w))
strU w = strr (text w)
