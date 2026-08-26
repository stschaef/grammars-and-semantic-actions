{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Regex parsers, end to end, with readable output.

   A regex is written in POSIX syntax as a string.  `reOf` elaborates it
   at typechecking time to an `RE`; `⟦ r ⟧` is its grammar; `decide-r` is
   the parser, folded from the Decidable combinators over the regex.  A
   semantic action then reads the parse tree back out, so each test below
   states the *result* and can be checked by eye.

   The alphabet is `UChar`, Unicode as 21 bits, so `c ≟ d` reduces;
   `String.Unicode`'s postulated oracle would leave every branch stuck.

   One step is not internal, and is marked where it happens: `parseRE`,
   the POSIX string → `RE` elaborator, is a metalanguage recursive
   descent.  Everything downstream of the `RE` is a `⊢`-term. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Regex.Examples where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Maybe as M
import Agda.Builtin.String as AS

open import Theory.Instances.Monoid.Unicode.Base
open import Theory.Instances.Monoid.Regex.Parse
open import Theory.Instances.Monoid.Lex.Regex UChar _≟U_ (ℓ-suc ℓ-zero)
  using (Lexicon ; lexer ; tokens ; yield ; Tokenisation ; NoTokenisation)

private
  ℓr : Level
  ℓr = ℓ-suc ℓ-zero

  -- `nothing` here is a *refutation* of every parse, not a dropped error:
  -- `semact-dec` is the bridge out of `DecTy`, and the refutation is
  -- still there in `decide-r` for anyone who wants it.
  matched : ∀ {n} (r : RE n) → AS.String → M.Maybe (List UChar)
  matched r = λ w → observe (decide-r r ℓr) (semact-dec (yield r)) (text w)

  -- ...displayed as text, so a case reads as text in, text out
  show : M.Maybe (List UChar) → M.Maybe AS.String
  show M.nothing = M.nothing
  show (M.just cs) = M.just (untext cs)


------------------------------------------------------------------------
-- 1. Each regex is named once; the table says what it consumes.

ident num strLit dotted date : RE notNullable
ident  = reOf "[[:alpha:]_][[:alnum:]_]*"
num    = reOf "-?[0-9]+"
strLit = reOf "\"[^\"]*\""
dotted = reOf "[a-z]+(\\.[a-z]+)*"
date   = reOf "[0-9]{4}-[0-9]{2}-[0-9]{2}"

_ : passes ((λ w → show (matched ident w)) at
    ( "buffer_size" ↦ M.just "buffer_size"
    ∷ "x"           ↦ M.just "x"
    ∷ "2fast"       ↦ M.nothing
    ∷ ""            ↦ M.nothing
    ∷ []))
_ = refl

_ : passes ((λ w → show (matched num w)) at
    ( "407"  ↦ M.just "407"
    ∷ "-407" ↦ M.just "-407"
    ∷ "4-07" ↦ M.nothing
    ∷ "-"    ↦ M.nothing
    ∷ []))
_ = refl

_ : passes ((λ w → show (matched strLit w)) at
    ( "\"\""            ↦ M.just "\"\""
    ∷ "\"hi there\""    ↦ M.just "\"hi there\""
    ∷ "\"unterminated"  ↦ M.nothing
    ∷ []))
_ = refl

_ : passes ((λ w → show (matched dotted w)) at
    ( "main"             ↦ M.just "main"
    ∷ "org.example.main" ↦ M.just "org.example.main"
    ∷ "org..main"        ↦ M.nothing
    ∷ "org."             ↦ M.nothing
    ∷ []))
_ = refl

_ : passes ((λ w → show (matched date w)) at
    ( "2026-08-26" ↦ M.just "2026-08-26"
    ∷ "26-08-26"   ↦ M.nothing
    ∷ "2026-8-26"  ↦ M.nothing
    ∷ []))
_ = refl

------------------------------------------------------------------------
-- 2. A lexer is a lexicon of those.  Its parse tree *is* the
--    tokenisation; the action below only names the rules.

data Tok : Type ℓ-zero where
  KW    : AS.String → Tok
  Ident : AS.String → Tok
  Num   : AS.String → Tok
  Op    : AS.String → Tok
  WS    : Tok

lexicon : Lexicon
lexicon =
    reOf "let|in|where"                  -- 0
  ∷ reOf "[[:alpha:]_][[:alnum:]_]*"     -- 1
  ∷ reOf "-?[0-9]+"                      -- 2
  ∷ reOf "[-+*/=<>]+"                    -- 3
  ∷ reOf "[ \t\n]+"                      -- 4
  ∷ []

private
  name : ℕ × List UChar → Tok
  name (0 , cs) = KW (untext cs)
  name (1 , cs) = Ident (untext cs)
  name (2 , cs) = Num (untext cs)
  name (3 , cs) = Op (untext cs)
  name (_ , cs) = WS

  lex : AS.String → M.Maybe (List Tok)
  lex w = observe (lexer lexicon)
            (semact-dec (semact-map (List.map name) (tokens lexicon))) (text w)
    where import Cubical.Data.List as List

------------------------------------------------------------------------
-- ...and the tokenisations, written out.

_ : passes (lex at
    ( "let x = 42"
        ↦ M.just (KW "let" ∷ WS ∷ Ident "x" ∷ WS ∷ Op "=" ∷ WS ∷ Num "42" ∷ [])
    ∷ "x+1"
        ↦ M.just (Ident "x" ∷ Op "+" ∷ Num "1" ∷ [])
    ∷ "where"
        ↦ M.just (KW "where" ∷ [])
    -- NOT maximal munch.  `where` is tried before the identifier rule and
    -- wins on a prefix, so "wherever" splits.  A greedy lexer would give
    -- `Ident "wherever"`.  This is the gap `Greedy/Base` exists to close;
    -- the case is here so it stays visible.
    ∷ "wherever"
        ↦ M.just (KW "where" ∷ Ident "ver" ∷ [])
    ∷ ""
        ↦ M.just []
    ∷ "x ? y"
        ↦ M.nothing
    ∷ []))
_ = refl
