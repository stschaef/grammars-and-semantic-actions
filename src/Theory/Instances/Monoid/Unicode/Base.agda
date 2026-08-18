{-# OPTIONS --lossy-unification #-}
{- A generic concrete Unicode lexicon for a free-monoid alphabet.

   The lexicon is the phase boundary: it specifies which Unicode characters
   denote which elements of the next alphabet.  `nothing` as a rule output
   consumes a character without emitting a token (whitespace); absence of a
   rule is a lexical error. -}
open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.Unicode.Base
  {ℓAlph}
  (Alphabet : Type ℓAlph) where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Relation.Nullary.Base using (yes ; no)
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)
open import Agda.Builtin.String as Text
open import String.Unicode using (UnicodeChar ; DiscreteUnicodeChar)
import Theory.Instances.Monoid.SemanticAction
import Theory.Instances.Monoid.Strings

-- A name table is the concise declaration a language normally supplies.
NameLexicon : Type ℓAlph
NameLexicon = List (UnicodeChar × Alphabet)

-- A complete lexer also admits ignored characters, such as whitespace.
Lexicon : Type ℓAlph
Lexicon = List (UnicodeChar × Maybe Alphabet)

names : NameLexicon → Lexicon
names [] = []
names ((c , a) ∷ rs) = (c , just a) ∷ names rs

lookup : UnicodeChar → Lexicon → Maybe (Maybe Alphabet)
lookup c [] = nothing
lookup c ((d , a) ∷ rs) with DiscreteUnicodeChar c d
... | yes _ = just a
... | no _ = lookup c rs

lexChars : Lexicon → List UnicodeChar → Maybe (List Alphabet)
lexChars rules [] = just []
lexChars rules (c ∷ cs) with lookup c rules
... | nothing = nothing
... | just nothing = lexChars rules cs
... | just (just a) with lexChars rules cs
... | nothing = nothing
... | just as = just (a ∷ as)

lex : Lexicon → Text.String → Maybe (List Alphabet)
lex rules text = lexChars rules (Text.primStringToList text)

-- The same lexicon is an internal semantic action from the free monoid on
-- Unicode characters.  This is the compiler-stage form; `lex` above remains
-- the convenient external entry point for literal test cases.
module Internal where
  isSetUnicodeChar : isSet UnicodeChar
  isSetUnicodeChar = Discrete→isSet DiscreteUnicodeChar

  module UnicodeAction = Theory.Instances.Monoid.SemanticAction UnicodeChar isSetUnicodeChar
  module UnicodeStrings = Theory.Instances.Monoid.Strings UnicodeChar isSetUnicodeChar

  lexAction : Lexicon
    → UnicodeAction.SemanticAction UnicodeStrings.String* (Maybe (List Alphabet))
  lexAction rules = UnicodeAction.scanAction (λ c → lookup c rules)
