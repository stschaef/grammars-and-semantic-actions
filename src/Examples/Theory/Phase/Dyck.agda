{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Dyck, end to end: Unicode source text, lexed to brackets, parsed. -}
open import Cubical.Foundations.Prelude

module Examples.Theory.Phase.Dyck where

open import Cubical.Data.List using (List ; [] ; _∷_)
import Cubical.Data.Maybe as Mb
import Agda.Builtin.String as AS

open import Cubical.Data.Unicode using (UChar ; _≟U_ ; text)
open import Theory.Instances.Monoid.Regex.Parse using (reOf)
-- re-exports `isSetAlphabet`, so `Phase` below is at the same instance
open import Theory.Instances.Monoid.Lex.Regex UChar _≟U_ (ℓ-suc ℓ-zero)
open import Theory.Instances.Monoid.Phase UChar isSetAlphabet

import Theory.Instances.Monoid.Grammars.Dyck as DG
open DG using (Br ; lp ; rp ; Dyck ; done ; nest ; S ; semactS)

import Theory.Instances.Monoid.Combinator.Decidable.Base
  Br DG._≟_ (ℓ-suc ℓ-zero) as Dec
import Theory.Instances.Monoid.Combinator.Grammars.Dyck
  Dec.DecAnswer as GDec

-- `Grammars/Dyck` names `Br` at top level instead of
-- taking the alphabet as a parameter, so `Tok` is `Br` on the nose.
Tok : Type ℓ-zero
Tok = Br

-- Priority order: `(`, `)`, one whitespace char.  Whitespace is a rule,
-- not a filter: the lexer's grammar must cover the whole input.
lexicon : Lexicon
lexicon = reOf "\\(" ∷ reOf "\\)" ∷ reOf "[ \t\n]" ∷ []

-- `nothing` is the skip; `anyOfr` branches are in rule order.
emitTok : SemanticAction (ty ⟦ tokenRE lexicon ⟧) (Mb.Maybe Tok)
emitTok =
  semact-⊕ (semact-pure (Mb.just lp))
    (semact-⊕ (semact-pure (Mb.just rp)) (semact-pure Mb.nothing))

lexPhase : Phase (lv (tokensRE lexicon)) Tok
lexPhase = record
  { Gr = ty ⟦ tokensRE lexicon ⟧
  ; dec = lexer lexicon
  ; emit = semact-skip* emitTok
  }

lex : AS.String → Mb.Maybe (List Tok)
lex s = runPhase lexPhase (text s)

parseToks : List Tok → Mb.Maybe Dyck
parseToks = Dec.observe GDec.dyck (Dec.semact-dec semactS)

-- `Phase` gives no composition, so the join is metalanguage; `Result` keeps the two failures apart.

data Result : Type ℓ-zero where
  lexFail   : Result
  parseFail : List Tok → Result
  ok        : Dyck → Result

pipeline : AS.String → Result
pipeline s = onLexed (lex s)
  where
  onParsed : List Tok → Mb.Maybe Dyck → Result
  onParsed ts Mb.nothing = parseFail ts
  onParsed ts (Mb.just d) = ok d

  onLexed : Mb.Maybe (List Tok) → Result
  onLexed Mb.nothing = lexFail
  onLexed (Mb.just ts) = onParsed ts (parseToks ts)

-- Every `refl` below is both phases computing.

_ : lex "(())" ≡ Mb.just (lp ∷ lp ∷ rp ∷ rp ∷ [])
_ = refl

_ : lex "( ( ) )" ≡ Mb.just (lp ∷ lp ∷ rp ∷ rp ∷ [])
_ = refl

_ : lex "" ≡ Mb.just []
_ = refl

-- `[` is in no rule, so the lexer refutes every tokenisation.
_ : lex "([)]" ≡ Mb.nothing
_ = refl

_ : pipeline "" ≡ ok done
_ = refl

_ : pipeline "()" ≡ ok (nest done done)
_ = refl

_ : pipeline "(())" ≡ ok (nest (nest done done) done)
_ = refl

_ : pipeline "(()())" ≡ ok (nest (nest done (nest done done)) done)
_ = refl

_ : pipeline "( ( ) )" ≡ ok (nest (nest done done) done)
_ = refl

_ : pipeline "  ( )  " ≡ ok (nest done done)
_ = refl

-- unknown character fails the lexer; unbalanced bracket fails the parser
_ : pipeline "([)]" ≡ lexFail
_ = refl

_ : pipeline "(()" ≡ parseFail (lp ∷ lp ∷ rp ∷ [])
_ = refl

_ : pipeline ")(" ≡ parseFail (rp ∷ lp ∷ [])
_ = refl

_ : pipeline "((()))" ≡ ok (nest (nest (nest done done) done) done)
_ = refl

_ : pipeline "(\n  ()\n)" ≡ ok (nest (nest done done) done)
_ = refl
