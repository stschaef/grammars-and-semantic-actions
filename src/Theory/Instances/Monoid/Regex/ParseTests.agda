{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Regexes written the way they are written everywhere else.

   `⟨| "…" |⟩` elaborates POSIX source at typechecking time, so the regex
   below is a value like any other and the decisions are the same ones as
   in `UnicodeTests` -- witnesses on a match, refutations on a miss. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Regex.ParseTests where

open import Cubical.Data.Bool using (true)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
import Agda.Builtin.String as AS

open import Theory.Instances.Monoid.Regex.Parse

private
  ℓr : Level
  ℓr = ℓ-suc ℓ-zero

  Yes : (s : AS.String) {p : IsJust (parseRE s)} (w : AS.String) → Type _
  Yes s {p} w = ty ⟦ reOf s {p} ⟧ (text w)

  No : (s : AS.String) {p : IsJust (parseRE s)} (w : AS.String) → Type _
  No s {p} w = ¬Ty (ty ⟦ reOf s {p} ⟧) (text w)

  yes : (s : AS.String) {p : IsJust (parseRE s)} (w : AS.String)
      → isYes (decide-r (reOf s {p}) ℓr (text w) tt) Eq.≡ true → Yes s {p} w
  yes s {p} w q = theYes (decide-r (reOf s {p}) ℓr (text w) tt) q

  no : (s : AS.String) {p : IsJust (parseRE s)} (w : AS.String)
     → isNo (decide-r (reOf s {p}) ℓr (text w) tt) Eq.≡ true → No s {p} w
  no s {p} w q = theNo (decide-r (reOf s {p}) ℓr (text w) tt) q

------------------------------------------------------------------------
-- concatenation, alternation, star

_ : Yes "ab" "ab"
_ = yes "ab" "ab" Eq.refl

_ : No "ab" "ba"
_ = no "ab" "ba" Eq.refl

_ : Yes "a|b" "b"
_ = yes "a|b" "b" Eq.refl

_ : Yes "(ab)*" "abab"
_ = yes "(ab)*" "abab" Eq.refl

_ : Yes "(ab)*" ""
_ = yes "(ab)*" "" Eq.refl

_ : No "(ab)*" "aba"
_ = no "(ab)*" "aba" Eq.refl

------------------------------------------------------------------------
-- postfix operators

_ : Yes "ab?c" "ac"
_ = yes "ab?c" "ac" Eq.refl

_ : Yes "ab?c" "abc"
_ = yes "ab?c" "abc" Eq.refl

_ : Yes "a+" "aaa"
_ = yes "a+" "aaa" Eq.refl

_ : No "a+" ""
_ = no "a+" "" Eq.refl

_ : Yes "a{3}" "aaa"
_ = yes "a{3}" "aaa" Eq.refl

_ : No "a{3}" "aa"
_ = no "a{3}" "aa" Eq.refl

_ : Yes "a{2,4}" "aaa"
_ = yes "a{2,4}" "aaa" Eq.refl

_ : No "a{2,4}" "aaaaa"
_ = no "a{2,4}" "aaaaa" Eq.refl

------------------------------------------------------------------------
-- classes, ranges, escapes

_ : Yes "[a-z]+" "hello"
_ = yes "[a-z]+" "hello" Eq.refl

_ : No "[a-z]+" "Hello"
_ = no "[a-z]+" "Hello" Eq.refl

_ : Yes "[^0-9]+" "abc"
_ = yes "[^0-9]+" "abc" Eq.refl

_ : No "[^0-9]+" "ab3"
_ = no "[^0-9]+" "ab3" Eq.refl

_ : Yes "\\d+" "407"
_ = yes "\\d+" "407" Eq.refl

_ : Yes "[[:alpha:]_][[:alnum:]_]*" "_foo42"
_ = yes "[[:alpha:]_][[:alnum:]_]*" "_foo42" Eq.refl

_ : No "[[:alpha:]_][[:alnum:]_]*" "42foo"
_ = no "[[:alpha:]_][[:alnum:]_]*" "42foo" Eq.refl

------------------------------------------------------------------------
-- the ones a real lexicon is made of

_ : Yes "-?[0-9]+" "-407"
_ = yes "-?[0-9]+" "-407" Eq.refl

_ : Yes "\"[^\"]*\"" "\"hi there\""
_ = yes "\"[^\"]*\"" "\"hi there\"" Eq.refl

_ : No "\"[^\"]*\"" "\"unterminated"
_ = no "\"[^\"]*\"" "\"unterminated" Eq.refl

_ : Yes "[ \t\n]+" " \t "
_ = yes "[ \t\n]+" " \t " Eq.refl

------------------------------------------------------------------------
-- Nullability is read off the elaborated regex, not asserted

_ : ∥ "a*" ∥ ≡ nullable
_ = refl

_ : ∥ "a+" ∥ ≡ notNullable
_ = refl

_ : ∥ "a?b" ∥ ≡ notNullable
_ = refl

_ : ∥ "a?b?" ∥ ≡ nullable
_ = refl
