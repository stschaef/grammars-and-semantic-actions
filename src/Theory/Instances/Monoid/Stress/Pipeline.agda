{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- How the STLC front end scales, measured by typechecking time.

   Four shapes, each grown along one axis: term depth, term width, binder
   depth, and type size.  Every case runs the whole of `Pipeline/STLC` --
   lex, parse, scope, typecheck -- so a regression anywhere shows up here.

   The sizes asserted below are the ones that keep this file cheap enough
   to sit inside `--build-library`.  To measure, raise the numeral and
   time `agda Theory/Instances/Monoid/Stress/Pipeline.agda`; the shape of
   the curve is the answer, not any single number. -}
open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.Stress.Pipeline where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Nat using (ℕ)
import Agda.Builtin.String as AS

open import Theory.Type.SemanticAction.Suite using (passes ; _at_ ; _↦_)
open import Theory.Instances.Monoid.Stress.Base using (repText ; nest)
open import Theory.Instances.Monoid.Pipeline.STLC using (check)

------------------------------------------------------------------------
-- Depth: `suc suc … suc zero`.  One nonterminal, one production, so this
-- is the parser's recursion cost with nothing else mixed in.

numeral : ℕ → AS.String
numeral n = nest n "suc " "zero"

depth : passes (check at
    ( numeral 4  ↦ "nat"
    ∷ numeral 8  ↦ "nat"
    ∷ numeral 16 ↦ "nat"
    ∷ []))
depth = refl

------------------------------------------------------------------------
-- Width: a chain of `let`s, each binding the previous.  This is the
-- scope checker's cost -- every occurrence is a lookup at growing depth
-- -- with the parse kept shallow.

lets : ℕ → AS.String
lets n = AS.primStringAppend (repText n "let x = zero in ") "x"

width : passes (check at
    ( lets 4  ↦ "nat"
    ∷ lets 8  ↦ "nat"
    ∷ lets 16 ↦ "nat"
    ∷ []))
width = refl

------------------------------------------------------------------------
-- Binder depth: `lam x : nat . lam x : nat . … x`.  Shadowing means the
-- answer is always the innermost binder, so the scope checker cannot
-- short-circuit, and each binder adds an arrow to the inferred type.

lams : ℕ → AS.String
lams n = nest n "lam x : nat . " "x"

arrows : ℕ → AS.String
arrows n = nest n "arr nat " "nat"

binders : passes (check at
    ( lams 1 ↦ arrows 1
    ∷ lams 2 ↦ arrows 2
    ∷ lams 4 ↦ arrows 4
    ∷ lams 8 ↦ arrows 8
    ∷ []))
binders = refl

------------------------------------------------------------------------
-- Type size: an annotation the typechecker must build and print, with
-- the term held to one binder.  This isolates `ATy` equality, which
-- every application and every `if` calls.

deepAnnotation : ℕ → AS.String
deepAnnotation n =
  AS.primStringAppend (AS.primStringAppend "lam x : " (arrows n)) " . x"

-- `lam x : A . x` has type `arr A A`, so the annotation is printed twice.
endo : AS.String → AS.String
endo a = AS.primStringAppend "arr " (AS.primStringAppend a (AS.primStringAppend " " a))

annotation : passes (check at
    ( deepAnnotation 1 ↦ endo (arrows 1)
    ∷ deepAnnotation 2 ↦ endo (arrows 2)
    ∷ deepAnnotation 4 ↦ endo (arrows 4)
    ∷ []))
annotation = refl

------------------------------------------------------------------------
-- The same two shapes at four times the size.  `anyOfr` is ordered
-- choice, so the tokeniser backtracks; if lexing were superlinear in the
-- input length rather than in the token count, it would show here first.

long : passes (check at
    ( numeral 32 ↦ "nat"
    ∷ lets 32    ↦ "nat"
    ∷ []))
long = refl
