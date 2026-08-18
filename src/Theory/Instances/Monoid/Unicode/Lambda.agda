{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Unicode concrete syntax for the lambda token alphabet.

   This is deliberately a monoid instance: Unicode text is lexed to the
   alphabet of the next free-monoid parser, and the parser itself remains an
   internal map of theory types. -}
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary.Base using (Discrete)
open import Cubical.Data.Maybe using (Maybe)
open import Cubical.Data.List using (List)
open import Cubical.Data.Sigma using (_×_)
open import String.Unicode using (UnicodeChar)

module Theory.Instances.Monoid.Unicode.Lambda
  (Name : Type ℓ-zero) (name≟ : Discrete Name)
  (nameLexicon : List (UnicodeChar × Name)) where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Unit using (tt)
import Agda.Builtin.String as AS

open import String.Unicode using (UnicodeChar ; DiscreteUnicodeChar)
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)

isSetUnicodeChar : isSet UnicodeChar
isSetUnicodeChar = Discrete→isSet DiscreteUnicodeChar
open import Theory.Instances.Monoid.Base using (MonEqns)
import Theory.Instances.Lambda.MonoidParser Name name≟ as P
import Theory.Instances.Monoid.Unicode.Base P.Token as Unicode
import Theory.Instances.Monoid.RecursiveDescent.Base P.Token P.isSetToken as RD
import Theory.Instances.Lambda.FrontEnd Name name≟ as FrontEnd
import Theory.Instances.Lambda.DeBruijn Name (Discrete→isSet name≟) as DB
import Theory.Instances.Monoid.Strings UnicodeChar isSetUnicodeChar as UnicodeStrings
import Theory.Instances.Monoid.Strings P.Token P.isSetToken as TokenStrings
import Theory.Instances.Monoid.SemanticAction UnicodeChar isSetUnicodeChar as UnicodeAction
import Theory.Instances.Monoid.SemanticAction P.Token P.isSetToken as TokenAction
import Theory.Type.SemanticAction.Pipeline

-- The language supplies names; lambda punctuation and whitespace are fixed
-- lexical entries.  Thus Unicode never leaks into the parser's `Name` type.
lexicon : Unicode.Lexicon
lexicon = ('λ' , just P.lambda) ∷ ('.' , just P.dot)
        ∷ ('(' , just P.lpar) ∷ (')' , just P.rpar)
        ∷ (' ' , nothing) ∷ Unicode.names (mapNames nameLexicon)
  where
  mapNames : List (UnicodeChar × Name) → Unicode.NameLexicon
  mapNames [] = []
  mapNames ((c , x) ∷ xs) = (c , P.ident x) ∷ mapNames xs

lex : AS.String → Maybe (List P.Token)
lex = Unicode.lex lexicon

parseTerm : List P.Token → Maybe P.Parsed
parseTerm ts = RD.complete (RD.parse P.parseTerm P.term-value ts)

scopeCheck : List P.Token → Maybe (DB.DB 0)
scopeCheck ts = join (RD.complete (RD.parse P.parseTerm FrontEnd.checkClosed ts))
  where
  join : {A : Type ℓ-zero} → Maybe (Maybe A) → Maybe A
  join nothing = nothing
  join (just x) = x

-- The complete internal compiler spine.  These three modules are genuinely
-- distinct free-monoid stages: Unicode input, lambda-token input, and the
-- lambda AST semantic action.
module Stage = Theory.Type.SemanticAction.Pipeline
  MonEqns UnicodeChar (λ _ → tt) UnicodeStrings.listPresentation
  MonEqns P.Token (λ _ → tt) TokenStrings.listPresentation
module TokenInput = TokenStrings.InputFrom
  MonEqns UnicodeChar (λ _ → tt) UnicodeStrings.listPresentation

parseAction : TokenAction.SemanticAction TokenStrings.String* (Maybe P.Parsed)
parseAction = RD.parse-complete P.parseTerm P.term-value

scopeAction : TokenAction.SemanticAction TokenStrings.String* (Maybe (DB.DB 0))
scopeAction = TokenAction.semact-map join (RD.parse-complete P.parseTerm FrontEnd.checkClosed)
  where
  join : Maybe (Maybe (DB.DB 0)) → Maybe (DB.DB 0)
  join nothing = nothing
  join (just x) = x

parsePipeline : UnicodeAction.SemanticAction UnicodeStrings.String* (Maybe P.Parsed)
parsePipeline = Stage.thenMaybe (Unicode.Internal.lexAction lexicon)
  TokenInput.stringInput parseAction

scopePipeline : UnicodeAction.SemanticAction UnicodeStrings.String* (Maybe (DB.DB 0))
scopePipeline = Stage.thenMaybe (Unicode.Internal.lexAction lexicon)
  TokenInput.stringInput scopeAction

runUnicode : {A : Type ℓ-zero}
  → UnicodeAction.SemanticAction UnicodeStrings.String* (Maybe A)
  → AS.String → Maybe A
runUnicode action text = action chars (UnicodeStrings.read chars tt) .fst
  where
  chars = AS.primStringToList text

parseUnicode : AS.String → Maybe P.Parsed
parseUnicode = runUnicode parsePipeline

checkUnicode : AS.String → Maybe (DB.DB 0)
checkUnicode = runUnicode scopePipeline
