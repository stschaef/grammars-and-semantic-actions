{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A lexicon, written as POSIX regexes.

   The previous version built its one-token parser by hand: `seq`ed
   `tok`s, a hand-ordered `<|>`, an `emit` action per branch, an
   `isSet Tok` by retraction, and a `¬Nullable` assembled from
   `⊗-¬Nullable`/`⊕-¬Nullable`.  All of it is gone -- a lexicon is a list
   of regexes and everything else is derived.

   Lexing itself has no semantic action: the parse tree of
   `(kw|ident|num|space)*` already *is* the tokenisation.  `tokens` below
   only reads it back out for display, which is the bridge to the next
   phase rather than part of this one. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Lex.Demo where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst)
open import Cubical.Data.Unit using (tt)
import Agda.Builtin.String as AS

open import Theory.Instances.Monoid.Unicode.Base
open import Theory.Instances.Monoid.Regex.Parse using (reOf)
open import Theory.Instances.Monoid.Lex.Regex UChar _≟U_ (ℓ-suc ℓ-zero)

------------------------------------------------------------------------
-- The lexicon, in priority order: keywords before identifiers.
--
--   0  let|in
--   1  [[:alpha:]_][[:alnum:]_]*
--   2  -?[0-9]+
--   3  [ \t\n]+

lexicon : Lexicon
lexicon =
    reOf "let|in"
  ∷ reOf "[[:alpha:]_][[:alnum:]_]*"
  ∷ reOf "-?[0-9]+"
  ∷ reOf "[ \t\n]+"
  ∷ []

-- the tokenisation, as rule index and lexeme
lexed : (w : AS.String) → Tokenisation lexicon (text w) → List (ℕ × List UChar)
lexed w t = tokens lexicon (text w) t .fst

------------------------------------------------------------------------
-- ...and it runs, showing what it lexed to.

letx : Tokenisation lexicon (text "let x")
letx = theYes (lexer lexicon (text "let x") tt) Eq.refl

_ : lexed "let x" letx
  ≡ (0 , ch 'l' ∷ ch 'e' ∷ ch 't' ∷ [])
  ∷ (3 , ch ' ' ∷ [])
  ∷ (1 , ch 'x' ∷ [])
  ∷ []
_ = refl

n42 : Tokenisation lexicon (text "-42")
n42 = theYes (lexer lexicon (text "-42") tt) Eq.refl

_ : lexed "-42" n42 ≡ (2 , ch '-' ∷ ch '4' ∷ ch '2' ∷ []) ∷ []
_ = refl

-- `?` is in no rule, so *nothing* tokenises this input
noq : NoTokenisation lexicon (text "x?")
noq = theNo (lexer lexicon (text "x?") tt) Eq.refl
