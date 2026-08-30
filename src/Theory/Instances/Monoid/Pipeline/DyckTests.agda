{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The Dyck front end, run on source text.

   The text suites state their answer as the balanced string `check`
   prints, so they read without knowing a constructor of `Dyck`; the last
   suite pins the structured result, so the parse tree is checked too.
   Every `refl` below is both phases computing. -}
open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.Pipeline.DyckTests where

open import Cubical.Data.List using (List ; [] ; _∷_)
import Cubical.Data.Maybe as Mb
import Agda.Builtin.String as AS

open import Theory.Type.SemanticAction.Suite using (passes ; _at_ ; _↦_)
open import Theory.Instances.Monoid.Pipeline.Dyck
  using (lex ; pipeline ; check ; Result ; lexFail ; parseFail ; ok)
open import Theory.Instances.Monoid.Grammars.Dyck
  using (lp ; rp ; Dyck ; done ; nest)

------------------------------------------------------------------------
-- Text in, text out.  The pipeline's answer on a balanced word is that
-- word again -- the empty word included, which prints as nothing at all.

balanced : passes (check at
    ( ""       ↦ ""
    ∷ "()"     ↦ "()"
    ∷ "(())"   ↦ "(())"
    ∷ "(()())" ↦ "(()())"
    ∷ "((()))" ↦ "((()))"
    ∷ []))
balanced = refl

-- Whitespace is a lexer rule that emits nothing, so layout changes the
-- source and nothing else.
whitespace-irrelevant : passes (check at
    ( "( ( ) )"    ↦ "(())"
    ∷ "  ( )  "    ↦ "()"
    ∷ "(\n  ()\n)" ↦ "(())"
    ∷ []))
whitespace-irrelevant = refl

------------------------------------------------------------------------
-- The two ways to be rejected, each by the phase whose business
-- it is.  This is what a `Maybe` at the end of the pipeline would hide.

-- The lexer: no rule spells `[` or `]`.
lex-errors : passes (check at
    ( "([)]" ↦ "lex error"
    ∷ "[]"   ↦ "lex error"
    ∷ []))
lex-errors = refl

-- The parser: the tokens are all real, the nesting is not.
parse-errors : passes (check at
    ( "(()" ↦ "parse error"
    ∷ ")("  ↦ "parse error"
    ∷ "("   ↦ "parse error"
    ∷ []))
parse-errors = refl

------------------------------------------------------------------------
-- The structured results, so the suites above pin a parse tree and not
-- only its printout.

-- Phase one alone: the token list, or its refusal.
lexing : passes (lex at
    ( "(())"    ↦ Mb.just (lp ∷ lp ∷ rp ∷ rp ∷ [])
    ∷ "( ( ) )" ↦ Mb.just (lp ∷ lp ∷ rp ∷ rp ∷ [])
    ∷ ""        ↦ Mb.just []
    ∷ "([)]"    ↦ Mb.nothing
    ∷ []))
lexing = refl

-- Both phases, against `Dyck` constructors and against the token list a
-- parse failure hands back.
parse-trees : passes (pipeline at
    ( ""       ↦ ok done
    ∷ "()"     ↦ ok (nest done done)
    ∷ "(())"   ↦ ok (nest (nest done done) done)
    ∷ "(()())" ↦ ok (nest (nest done (nest done done)) done)
    ∷ "((()))" ↦ ok (nest (nest (nest done done) done) done)
    ∷ "(()"    ↦ parseFail (lp ∷ lp ∷ rp ∷ [])
    ∷ ")("     ↦ parseFail (rp ∷ lp ∷ [])
    ∷ "([)]"   ↦ lexFail
    ∷ []))
parse-trees = refl
