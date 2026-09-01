{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- POSIX classes on real text.  A match is the parse itself; a non-match is a
   refutation of every parse -- `Maybe` would have discarded it. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Equality as Eq

module Examples.Theory.Regex.Unicode where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Bool using (Bool ; true)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
import Agda.Builtin.String as AS

open import Theory.Instances.Monoid.Regex.Unicode

private
  ℓr : Level
  ℓr = ℓ-suc ℓ-zero

  Yes : ∀ {n} (r : RE n) (s : AS.String) → Type _
  Yes r s = ty ⟦ r ⟧ (text s)

  No : ∀ {n} (r : RE n) (s : AS.String) → Type _
  No r s = ¬Ty (ty ⟦ r ⟧) (text s)

  yes : ∀ {n} (r : RE n) (s : AS.String)
      → isYes (decide-r r ℓr (text s) tt) Eq.≡ true → Yes r s
  yes r s p = theYes (decide-r r ℓr (text s) tt) p

  no : ∀ {n} (r : RE n) (s : AS.String)
     → isNo (decide-r r ℓr (text s) tt) Eq.≡ true → No r s
  no r s p = theNo (decide-r r ℓr (text s) tt) p

-- `[a-z]+` -- a range, which a general alphabet cannot express

lowers : RE notNullable
lowers = lowerR +r

lowers-abc : Yes lowers "abc"
lowers-abc = yes lowers "abc" Eq.refl

lowers-aBc : No lowers "aBc"
lowers-aBc = no lowers "aBc" Eq.refl

lowers-ε : No lowers ""
lowers-ε = no lowers "" Eq.refl

-- `[[:alpha:]_][[:alnum:]_]*` -- a C identifier

ident : RE notNullable
ident = bracketR (classI isAlpha ∷ chI '_' ∷ [])
   ⊗r (bracketR (classI isAlnum ∷ chI '_' ∷ []) *r)

satChar : {P : UChar → Bool} → SemanticAction (satG P) UChar
satChar m (x , _) = x .fst , tt

identChars : SemanticAction (ty ⟦ ident ⟧) (UChar × List UChar)
identChars = semact-⊗₂ satChar (semact-* satChar)

readIdent : (s : AS.String) → Yes ident s → UChar × List UChar
readIdent s w = identChars (text s) w .fst

_ : readIdent "_foo" (yes ident "_foo" Eq.refl)
  ≡ (ch '_' , ch 'f' ∷ ch 'o' ∷ ch 'o' ∷ [])
_ = refl

ident-x : Yes ident "x"
ident-x = yes ident "x" Eq.refl

ident-42foo : No ident "42foo"
ident-42foo = no ident "42foo" Eq.refl

-- `-?[0-9]+` -- a signed integer

int : RE notNullable
int = (charR '-') ?r ⊗r (digitR +r)

int-407 : Yes int "407"
int-407 = yes int "407" Eq.refl

int-neg : Yes int "-407"
int-neg = yes int "-407" Eq.refl

int-bad : No int "4-07"
int-bad = no int "4-07" Eq.refl

-- `"[^"]*"` -- the complement a list of disjuncts could not express over a 21-bit alphabet

strLit : RE notNullable
strLit = charR '"' ⊗r (bracketNotR (chI '"' ∷ []) *r) ⊗r charR '"'

strLit-empty : Yes strLit "\"\""
strLit-empty = yes strLit "\"\"" Eq.refl

strLit-body : Yes strLit "\"hi there\""
strLit-body = yes strLit "\"hi there\"" Eq.refl

strLit-open : No strLit "\"unterminated"
strLit-open = no strLit "\"unterminated" Eq.refl

-- a literal word, and `[0-9]{2,4}`

kw : RE notNullable
kw = strU "let"

kw-yes : Yes kw "let"
kw-yes = yes kw "let" Eq.refl

kw-no : No kw "le"
kw-no = no kw "le" Eq.refl

twoToFour : RE notNullable
twoToFour = betweenr 2 2 digitR

n2 : Yes twoToFour "42"
n2 = yes twoToFour "42" Eq.refl

n4 : Yes twoToFour "4207"
n4 = yes twoToFour "4207" Eq.refl

n1 : No twoToFour "4"
n1 = no twoToFour "4" Eq.refl

n5 : No twoToFour "42071"
n5 = no twoToFour "42071" Eq.refl
