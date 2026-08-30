{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The front end of `Pipeline/STLC`, run on source text.

   Every case is a program written the way a reader would write it and an
   answer written the way `showTy` prints one, so the suite is legible
   without knowing a single constructor of `Tok`, `ATm` or `ATy`.  Each
   `refl` below is all four passes computing. -}
open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.Pipeline.STLCTests where

open import Cubical.Data.List using (List ; [] ; _∷_)
import Agda.Builtin.String as AS

open import Theory.Type.SemanticAction.Suite using (passes ; _at_ ; _↦_)
open import Theory.Instances.Monoid.Pipeline.STLC using (check)

------------------------------------------------------------------------
-- Programs that typecheck.  The answer is the inferred type, printed.

typechecks : passes (check at
    ( "zero"                            ↦ "nat"
    ∷ "true"                            ↦ "bool"
    ∷ "suc zero"                        ↦ "nat"
    ∷ "lam x : nat . x"                 ↦ "arr nat nat"
    ∷ "lam x : bool . zero"             ↦ "arr bool nat"
    ∷ "app lam x : nat . x zero"        ↦ "nat"
    ∷ "pair zero true"                  ↦ "prod nat bool"
    ∷ "fst pair zero true"              ↦ "nat"
    ∷ "snd pair zero true"              ↦ "bool"
    ∷ "nil : nat"                       ↦ "list nat"
    ∷ "cons zero nil : nat"             ↦ "list nat"
    ∷ "if true then zero else suc zero" ↦ "nat"
    ∷ "let x = zero in x"               ↦ "nat"
    ∷ "let x = zero in suc x"           ↦ "nat"
    ∷ "lam f : arr nat nat . f"         ↦ "arr arr nat nat arr nat nat"
    ∷ []))
typechecks = refl

-- Whitespace and line breaks change the source and nothing else.
layout-irrelevant : passes (check at
    ( "  lam x : nat . x  "     ↦ "arr nat nat"
    ∷ "lam\n  x : nat .\n  x"   ↦ "arr nat nat"
    ∷ "app\tlam x : nat . x\tzero" ↦ "nat"
    ∷ []))
layout-irrelevant = refl

------------------------------------------------------------------------
-- The four ways to be rejected, each by the pass whose business
-- it is.  This is what a `Maybe` at the end of the pipeline would hide.

-- The lexer: no rule spells `@`, or `y`.
lex-errors : passes (check at
    ( "zero @ zero" ↦ "lex error"
    ∷ "lam y : nat . y" ↦ "lex error"
    ∷ []))
lex-errors = refl

-- The parser: the tokens are all real, the shape is not.
parse-errors : passes (check at
    ( "lam x . x"                ↦ "parse error"   -- binder with no annotation
    ∷ "if true then zero"        ↦ "parse error"   -- `if` with no `else`
    ∷ "natrec zero zero"         ↦ "parse error"   -- recursor short an argument
    ∷ "nat"                      ↦ "parse error"   -- a type is not a term
    ∷ "let x = zero in x zero"   ↦ "parse error"   -- one token too many
    ∷ []))
parse-errors = refl

-- The scope checker: it parses, but the name is free.
scope-errors : passes (check at
    ( "x"                       ↦ "scope error"
    ∷ "suc x"                   ↦ "scope error"
    ∷ "let x = zero in n"       ↦ "scope error"
    ∷ "app lam x : nat . x g"   ↦ "scope error"
    ∷ []))
scope-errors = refl

-- The typechecker: it scopes, but the types do not agree.
type-errors : passes (check at
    ( "suc true"                        ↦ "type error"
    ∷ "app lam x : nat . x true"        ↦ "type error"
    ∷ "if zero then zero else zero"     ↦ "type error"
    ∷ "cons true nil : nat"             ↦ "type error"
    ∷ "fst zero"                        ↦ "type error"
    ∷ []))
type-errors = refl
