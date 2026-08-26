{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Regex parsers, end to end.

   A regex is written in POSIX syntax as a string.  `reOf` elaborates it
   at typechecking time to an `RE`, whose denotation `⟦ r ⟧` is a grammar,
   whose parser `decide-r` is built by folding the Decidable combinators
   over the regex.  Running it on real text gives a parse or a refutation
   of every parse -- never a `Bool`.

   The alphabet is `UChar`, Unicode as an internal type: 21 bits, so
   `c ≟ d` reduces.  `String.Unicode`'s postulated oracle would leave
   every branch stuck and nothing below would compute.

   One thing here is not internal, and is marked where it happens:
   `parseRE`, which turns the POSIX *string* into an `RE`, is a
   metalanguage recursive descent.  Everything downstream of the `RE` is
   a `⊢`-term. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Regex.Examples where

open import Cubical.Data.Bool using (true)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst)
open import Cubical.Data.Unit using (tt)
import Agda.Builtin.String as AS

open import Theory.Instances.Monoid.Unicode.Base
open import Theory.Instances.Monoid.Regex.Parse
open import Theory.Instances.Monoid.Lex.Regex UChar _≟U_ (ℓ-suc ℓ-zero)
  using (Lexicon ; lexer ; tokens ; Tokenisation ; NoTokenisation)

private
  ℓr : Level
  ℓr = ℓ-suc ℓ-zero

  -- a parse of `w` as `r`, or a refutation of every parse
  Match   = λ (s : AS.String) {p : IsJust (parseRE s)} (w : AS.String)
          → ty ⟦ reOf s {p} ⟧ (text w)
  NoMatch = λ (s : AS.String) {p : IsJust (parseRE s)} (w : AS.String)
          → ¬Ty (ty ⟦ reOf s {p} ⟧) (text w)

  match : (s : AS.String) {p : IsJust (parseRE s)} (w : AS.String)
        → isYes (decide-r (reOf s {p}) ℓr (text w) tt) Eq.≡ true
        → Match s {p} w
  match s {p} w q = theYes (decide-r (reOf s {p}) ℓr (text w) tt) q

  noMatch : (s : AS.String) {p : IsJust (parseRE s)} (w : AS.String)
          → isNo (decide-r (reOf s {p}) ℓr (text w) tt) Eq.≡ true
          → NoMatch s {p} w
  noMatch s {p} w q = theNo (decide-r (reOf s {p}) ℓr (text w) tt) q

------------------------------------------------------------------------
-- 1. A few regex parsers, each written the way a regex is written.

-- an identifier
_ : Match "[[:alpha:]_][[:alnum:]_]*" "buffer_size"
_ = match "[[:alpha:]_][[:alnum:]_]*" "buffer_size" Eq.refl

_ : NoMatch "[[:alpha:]_][[:alnum:]_]*" "2fast"
_ = noMatch "[[:alpha:]_][[:alnum:]_]*" "2fast" Eq.refl

-- a signed integer
_ : Match "-?[0-9]+" "-407"
_ = match "-?[0-9]+" "-407" Eq.refl

_ : NoMatch "-?[0-9]+" "4-07"
_ = noMatch "-?[0-9]+" "4-07" Eq.refl

-- a string literal: the complement class is why `satr` takes a predicate
_ : Match "\"[^\"]*\"" "\"hi there\""
_ = match "\"[^\"]*\"" "\"hi there\"" Eq.refl

_ : NoMatch "\"[^\"]*\"" "\"unterminated"
_ = noMatch "\"[^\"]*\"" "\"unterminated" Eq.refl

-- a dotted name, exercising alternation under a star
_ : Match "[a-z]+(\\.[a-z]+)*" "org.example.main"
_ = match "[a-z]+(\\.[a-z]+)*" "org.example.main" Eq.refl

_ : NoMatch "[a-z]+(\\.[a-z]+)*" "org..main"
_ = noMatch "[a-z]+(\\.[a-z]+)*" "org..main" Eq.refl

-- counted repetition
_ : Match "[0-9]{4}-[0-9]{2}-[0-9]{2}" "2026-08-26"
_ = match "[0-9]{4}-[0-9]{2}-[0-9]{2}" "2026-08-26" Eq.refl

_ : NoMatch "[0-9]{4}-[0-9]{2}-[0-9]{2}" "26-08-26"
_ = noMatch "[0-9]{4}-[0-9]{2}-[0-9]{2}" "26-08-26" Eq.refl

------------------------------------------------------------------------
-- 2. A lexer is a lexicon of those, and its parse tree is the
--    tokenisation.  Priority is the list order: keywords first.
--
--      0  let|in|where
--      1  [[:alpha:]_][[:alnum:]_]*
--      2  -?[0-9]+
--      3  [-+*/=<>]+
--      4  [ \t\n]+

lexicon : Lexicon
lexicon =
    reOf "let|in|where"
  ∷ reOf "[[:alpha:]_][[:alnum:]_]*"
  ∷ reOf "-?[0-9]+"
  ∷ reOf "[-+*/=<>]+"
  ∷ reOf "[ \t\n]+"
  ∷ []

lexed : (w : AS.String) → Tokenisation lexicon (text w) → List (ℕ × List UChar)
lexed w t = tokens lexicon (text w) t .fst

------------------------------------------------------------------------
-- ...run on real text.  The result says which rule matched over which
-- characters, in order -- no semantic action involved.

src : Tokenisation lexicon (text "let x = 42")
src = theYes (lexer lexicon (text "let x = 42") tt) Eq.refl

_ : lexed "let x = 42" src
  ≡ (0 , ch 'l' ∷ ch 'e' ∷ ch 't' ∷ [])
  ∷ (4 , ch ' ' ∷ [])
  ∷ (1 , ch 'x' ∷ [])
  ∷ (4 , ch ' ' ∷ [])
  ∷ (3 , ch '=' ∷ [])
  ∷ (4 , ch ' ' ∷ [])
  ∷ (2 , ch '4' ∷ ch '2' ∷ [])
  ∷ []
_ = refl

-- `?` is in no rule, so *nothing* tokenises this input
_ : NoTokenisation lexicon (text "x ? y")
_ = theNo (lexer lexicon (text "x ? y") tt) Eq.refl
