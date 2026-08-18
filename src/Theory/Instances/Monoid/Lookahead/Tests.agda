{- The lookahead cover must not merely typecheck: its `total` half is the
   parser's dispatch, so it has to reduce on real lexed input. -}
open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.Lookahead.Tests where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Sigma using (_×_ ; _,_)
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)
import Agda.Builtin.String as AS

open import String.Unicode using (UnicodeChar ; DiscreteUnicodeChar)

isSetUnicodeChar : isSet UnicodeChar
isSetUnicodeChar = Discrete→isSet DiscreteUnicodeChar

------------------------------------------------------------------------
-- Source text, classified by one character of lookahead.

module Chars where
  open import Theory.Instances.Monoid.Lookahead.Base UnicodeChar isSetUnicodeChar

  classify : AS.String → M₁
  classify s = Λ-total (AS.primStringToList s) tt .fst
    where open import Cubical.Data.Unit using (tt)

  _ : classify "" ≡ ε₁
  _ = refl

  _ : classify "λx.x" ≡ tk 'λ'
  _ = refl

  _ : classify "(f x)" ≡ tk '('
  _ = refl

  _ : classify "  λf.λx.(f (f x))" ≡ tk ' '
  _ = refl

------------------------------------------------------------------------
-- The same text after lexing, on the alphabet of lambda tokens.  The
-- lexicon is the real one: punctuation fixed, names from the language.

module Tokens where
  open import Cubical.Data.Unit using (tt)
  import Theory.Instances.Monoid.Unicode.Base UnicodeChar as U

  lexicon : U.Lexicon
  lexicon = ('λ' , just 'λ') ∷ ('.' , just '.')
          ∷ ('(' , just '(') ∷ (')' , just ')')
          ∷ (' ' , nothing)
          ∷ U.names (('f' , 'f') ∷ ('x' , 'x') ∷ ('y' , 'y') ∷ [])

  tokens : AS.String → List UnicodeChar
  tokens s with U.lex lexicon s
  ... | just ts = ts
  ... | nothing = []

  open import Theory.Instances.Monoid.Lookahead.Base UnicodeChar isSetUnicodeChar

  classify : AS.String → M₁
  classify s = Λ-total (tokens s) tt .fst

  -- the lexer really runs: whitespace is dropped
  _ : tokens "  λx.x" ≡ 'λ' ∷ 'x' ∷ '.' ∷ 'x' ∷ []
  _ = refl

  _ : classify "" ≡ ε₁
  _ = refl

  _ : classify "  λx.x" ≡ tk 'λ'
  _ = refl

  _ : classify "(f x)" ≡ tk '('
  _ = refl

  _ : classify "x" ≡ tk 'x'
  _ = refl

  _ : classify " λf.λx.(f (f x))" ≡ tk 'λ'
  _ = refl
