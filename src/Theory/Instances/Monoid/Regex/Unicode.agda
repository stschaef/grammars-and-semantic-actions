{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- POSIX regular expressions at Unicode.

   Ranges need an ordering, which a general alphabet has not got; `UChar`
   has, through `code`.  So this layer exists and `Regex.Notation` does not
   mention ranges.

   Every class is a *predicate* first and a regex second, which is what
   makes the complements free: `[:digit:]` and `\D` are `satr isDigit` and
   `satr (not ∘ isDigit)`.  With a list of disjuncts instead, the
   complement over a 21-bit alphabet would be two million of them. -}
open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.Regex.Unicode where

open import Cubical.Data.Bool using (Bool ; true ; false ; _and_ ; _or_ ; not)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Nat using (ℕ)
import Agda.Builtin.Nat as AN
import Agda.Builtin.Char as AC
import Agda.Builtin.String as AS

open import Theory.Instances.Monoid.Unicode.Base public
open import Theory.Instances.Monoid.Regex.Notation UChar _≟U_ (ℓ-suc ℓ-zero)
  public

private
  _≤ᵇ_ : ℕ → ℕ → Bool
  m ≤ᵇ n = not (AN._<_ n m)

  -- `primCharToNat` already *is* the code point, so a comparison against a
  -- literal needs no `ch`/`code` round trip -- only the input is converted
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
ranger : AC.Char → AC.Char → RE notNullable
ranger lo hi = satr (inRange lo hi)

-- `[c]`
charr : AC.Char → RE notNullable
charr c = ⟨ ch c ⟩r

digitr alphar alnumr upperr lowerr xdigitr : RE notNullable
spacer blankr punctr cntrlr printr graphr wordr : RE notNullable
digitr  = satr isDigit
alphar  = satr isAlpha
alnumr  = satr isAlnum
upperr  = satr isUpper
lowerr  = satr isLower
xdigitr = satr isXDigit
spacer  = satr isSpace
blankr  = satr isBlank
punctr  = satr isPunct
cntrlr  = satr isCntrl
printr  = satr isPrint
graphr  = satr isGraph
wordr   = satr isWord

-- `\D`, `\S`, `\W` -- free, because a class is a predicate
notDigitr notSpacer notWordr : RE notNullable
notDigitr = satr λ c → not (isDigit c)
notSpacer = satr λ c → not (isSpace c)
notWordr  = satr λ c → not (isWord c)

-- `.` -- POSIX's dot excludes the newline
dotr : RE notNullable
dotr = satr λ c → not (eqc '\n' c)

-- Bracket expressions.  `[abc0-9[:alpha:]]` is a union of items, and its
-- negation is the same list read through `not`.

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
bracketr : List Item → RE notNullable
bracketr is = satr (anyItem is)

-- `[^…]`
bracketNotr : List Item → RE notNullable
bracketNotr is = satr λ c → not (anyItem is c)

-- A literal word, written as text
--
--   strU "let"   rather than   strr (ch 'l' ∷ ch 'e' ∷ ch 't' ∷ [])

strU : (w : AS.String) → RE (nullb (text w))
strU w = strr (text w)
