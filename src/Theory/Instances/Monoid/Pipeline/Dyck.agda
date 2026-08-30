{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Dyck, end to end: Unicode source text, lexed to brackets, parsed.

   Phase one is a `Phase Tok` over `UChar`; phase two is the existing Dyck
   parser, run over `Tok` rather than over characters.  Whitespace is
   skipped by *emitting nothing*, which is all `List Out` has to say. -}
open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.Pipeline.Dyck where

open import Cubical.Data.List using (List ; [] ; _∷_)
import Cubical.Data.Maybe as Mb
import Agda.Builtin.String as AS

open import Theory.Instances.Monoid.Unicode.Base using (UChar ; _≟U_ ; text)
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

-- Exactly the two brackets: whitespace never becomes a token, so there is
-- nothing else for the parser to see.
--
-- This is `Br` and not a fresh datatype because `Grammars/Dyck` and
-- `Combinator/Grammars/Dyck` name `Br` at top level rather than taking the
-- alphabet as a module parameter.  The bodies of both are already generic
-- -- everything goes through `lp`, `rp` and `_≟_` -- so parameterising
-- them is mechanical; see the report.  Nothing below depends on which
-- two-element type this is.
Tok : Type ℓ-zero
Tok = Br

-- Three POSIX rules, in priority order: `(`, `)`, one whitespace
-- character.  Whitespace is a rule and not a filter, because the lexer's
-- grammar has to cover the whole input.
lexicon : Lexicon
lexicon = reOf "\\(" ∷ reOf "\\)" ∷ reOf "[ \t\n]" ∷ []

-- What one lexeme hands on.  `nothing` is the skip; the shape of
-- `anyOfr` is `( ⊕r ( ) ⊕r ws )`, so the branches are read off in rule
-- order.
emitTok : SemanticAction (ty ⟦ tokenRE lexicon ⟧) (Mb.Maybe Tok)
emitTok =
  semact-⊕ (semact-pure (Mb.just lp))
    (semact-⊕ (semact-pure (Mb.just rp)) (semact-pure Mb.nothing))

lexPhase : Phase (lv (tokensRE lexicon)) Tok
lexPhase = record
  { Ty = ty ⟦ tokensRE lexicon ⟧
  ; dec = lexer lexicon
  ; emit = semact-skip* emitTok
  }

lex : AS.String → Mb.Maybe (List Tok)
lex s = runPhase lexPhase (text s)

parseToks : List Tok → Mb.Maybe Dyck
parseToks = Dec.observe GDec.dyck (Dec.semact-dec semactS)

-- `Phase` gives no composition, so the join is metalanguage.  Keeping the
-- two failures apart is the point: `Maybe (Maybe Dyck)` would say only
-- that something went wrong.

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

------------------------------------------------------------------------
-- Display.
--
-- The canonical readback: a `Dyck` re-printed as the balanced string it
-- is.  `nest inner rest` is the production `S -> ( S ) S`, so it prints
-- as its bracket pair around `inner`, followed by `rest`.  With this a
-- test states its expectation as text rather than as a constructor tree.

showDyck : Dyck → AS.String
showDyck done = ""
showDyck (nest inner rest) =
  AS.primStringAppend "("
    (AS.primStringAppend (showDyck inner)
      (AS.primStringAppend ")" (showDyck rest)))

-- The pipeline's answer, as text: the re-printed tree, or which phase
-- refused.  This is what the suites in `Pipeline/DyckTests` compare.
report : Result → AS.String
report lexFail = "lex error"
report (parseFail _) = "parse error"
report (ok d) = showDyck d

check : AS.String → AS.String
check s = report (pipeline s)
