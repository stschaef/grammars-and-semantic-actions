{-# OPTIONS --lossy-unification #-}
{- The same parser, elaborated in two models.

   `Semantics.Examples.StarParser` is written once, against an
   arbitrary model. Below it is instantiated twice, and in each case the
   elaborated type is spelled out.

   Families of sets over strings: a term is a string-indexed function,
   so the parser takes a string `w` together with a parse of it as a
   `char *`, and returns either a parse of `w` as a run of `c`s or a
   failure token. The parse tree it returns is indexed by `w`, so it is
   intrinsically a parse *of that string*.

   Just sets: the string index is forgotten and a term is an ordinary
   function. `char *` denotes `List ⟨ char ⟩` and `＂ c ＂ *` denotes
   `List Unit`, so the very same code elaborates to a plain Agda program
   taking a list of characters to a list of tokens or a failure.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Relation.Nullary.Base

module Semantics.Examples.StarParserDemo
  (Alphabet : hSet ℓ-zero)
  (DiscA : Discrete ⟨ Alphabet ⟩)
  (c : ⟨ Alphabet ⟩)
  where

open import Cubical.Data.List using (List)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet hiding (⟨_⟩)
open import Grammar.Literal.Base Alphabet
open import Term.Base Alphabet

import Semantics.Notation
import Semantics.Examples.StarParser

open import Semantics.Instances.Families Alphabet
open import Semantics.Instances.FamiliesInductive Alphabet
open import Semantics.Instances.Sets
open import Semantics.Instances.SetsInductive

------------------------------------------------------------------------
-- 1. Families of sets over strings
------------------------------------------------------------------------

module Fam where
  private
    litA : ⟨ Alphabet ⟩ → SetGrammar ℓ-zero
    litA a = literal a , isSetGrammarLiteral a

  module N = Semantics.Notation Literals
  module P = Semantics.Examples.StarParser Literals DiscA

  -- The two Kleene stars the parser needs, from
  -- `FamiliesInitialAlgebra`.
  private
    Ichar = ⋆Alg ℓ-zero Alphabet litA N.char
    Ic = ⋆Alg ℓ-zero Alphabet litA N.＂ c ＂

  string cstar Result : SetGrammar ℓ-zero
  string = P.string c Ichar Ic
  cstar = P.cstar c Ichar Ic
  Result = P.Result c Ichar Ic

  -- Elaborated: a string-indexed function. Given a string `w` and a
  -- parse of it as a sequence of characters, produce a parse of `w` as
  -- a run of `c`s, or fail.
  parse : ∀ (w : String) → string .fst w → Result .fst w
  parse = P.parse c Ichar Ic

------------------------------------------------------------------------
-- 2. Just sets
------------------------------------------------------------------------

module Set where
  module N = Semantics.Notation (SetsOn ℓ-zero Alphabet)
  module P = Semantics.Examples.StarParser (SetsOn ℓ-zero Alphabet) DiscA

  private
    Ichar = ⋆InitSets ℓ-zero Alphabet N.char
    Ic = ⋆InitSets ℓ-zero Alphabet N.＂ c ＂

  string cstar Result : hSet ℓ-zero
  string = P.string c Ichar Ic
  cstar = P.cstar c Ichar Ic
  Result = P.Result c Ichar Ic

  -- The denotations are ordinary types: `char *` is a list of
  -- characters, `＂ c ＂ *` is a list of featureless tokens.
  _ : ⟨ string ⟩ ≡ List (Σ[ _ ∈ ⟨ Alphabet ⟩ ] Unit*)
  _ = refl

  _ : ⟨ cstar ⟩ ≡ List (Unit* {ℓ-zero})
  _ = refl

  -- Elaborated: a plain Agda function.
  parse : ⟨ string ⟩ → ⟨ Result ⟩
  parse = P.parse c Ichar Ic
