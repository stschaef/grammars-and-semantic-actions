{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The simply typed lambda calculus, end to end: Unicode source text,
   lexed to tokens, parsed, scope checked, type checked.

   Four phases, four distinguishable failures.  The point of keeping them
   apart is that a `Maybe` at the end would say only that something went
   wrong; `Result` says which pass refused, and the passes that ran first
   hand on what they built.

   The concrete syntax is prefix throughout -- `app f x`, `arr A B` --
   because that is what makes the grammar LL(1); see the table in
   `Combinator/Decidable/STLC`. -}
open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.Pipeline.STLC where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Maybe as Mb
import Agda.Builtin.String as AS

open import Theory.Type.Decidable.DiscreteEq using (nth)
open import Theory.Instances.Monoid.Unicode.Base using (UChar ; _≟U_ ; text)
open import Theory.Instances.Monoid.Regex.Parse using (reOf)
-- re-exports `isSetAlphabet`, so `Phase` below is at the same instance
open import Theory.Instances.Monoid.Lex.Regex UChar _≟U_ (ℓ-suc ℓ-zero)
open import Theory.Instances.Monoid.Phase UChar isSetAlphabet

open import Theory.Instances.Monoid.Combinator.Decidable.STLC
  using ( Tok
        ; kbool ; knat ; karr ; kprod ; klist
        ; ktrue ; kfalse ; kif ; kthen ; kelse
        ; kzero ; ksuc ; knatrec ; klam ; kcolon ; kdot ; kapp
        ; kpair ; kfst ; ksnd ; knil ; kcons ; kfoldr
        ; klet ; kassign ; kin ; vf ; vg ; vn ; vx ; vxs
        ; ATy ; Bo ; Na ; Ar ; Pr ; Li
        ; ATm ; BTm
        ; astOf ; scopeOf ; tyOf )

------------------------------------------------------------------------
-- 1.  The lexicon.
--
-- POSIX rules in priority order.  A keyword must precede any variable it
-- starts with -- `nat` before `n`, `xs` before `x` -- because `anyOfr` is
-- *ordered* choice, and a longer keyword must precede its own prefix, so
-- `natrec` comes before `nat`.  Whitespace is a rule and not a filter,
-- because the lexer's grammar has to cover the whole input.

lexicon : Lexicon
lexicon =
  -- keywords, longest-first where one is a prefix of another
    reOf "natrec" ∷ reOf "nat"  ∷ reOf "bool"  ∷ reOf "arr"   ∷ reOf "prod"
  ∷ reOf "list"   ∷ reOf "true" ∷ reOf "false" ∷ reOf "if"    ∷ reOf "then"
  ∷ reOf "else"   ∷ reOf "zero" ∷ reOf "suc"   ∷ reOf "lam"   ∷ reOf "app"
  ∷ reOf "pair"   ∷ reOf "fst"  ∷ reOf "snd"   ∷ reOf "nil"   ∷ reOf "cons"
  ∷ reOf "foldr"  ∷ reOf "let"  ∷ reOf "in"
  -- punctuation
  ∷ reOf ":"      ∷ reOf "\\."  ∷ reOf "="
  -- the five variables, `xs` before `x`
  ∷ reOf "xs"     ∷ reOf "f"    ∷ reOf "g"     ∷ reOf "n"     ∷ reOf "x"
  -- the skip
  ∷ reOf "[ \t\n]"
  ∷ []

-- The token each rule yields, in the same order.  Whitespace is
-- `nothing`, which is how `semact-skip*` drops it.
tokenOfRule : ℕ → Mb.Maybe Tok
tokenOfRule = nth Mb.nothing table
  where
  table : List (Mb.Maybe Tok)
  table =
      Mb.just knatrec ∷ Mb.just knat  ∷ Mb.just kbool  ∷ Mb.just karr
    ∷ Mb.just kprod   ∷ Mb.just klist ∷ Mb.just ktrue  ∷ Mb.just kfalse
    ∷ Mb.just kif     ∷ Mb.just kthen ∷ Mb.just kelse  ∷ Mb.just kzero
    ∷ Mb.just ksuc    ∷ Mb.just klam  ∷ Mb.just kapp   ∷ Mb.just kpair
    ∷ Mb.just kfst    ∷ Mb.just ksnd  ∷ Mb.just knil   ∷ Mb.just kcons
    ∷ Mb.just kfoldr  ∷ Mb.just klet  ∷ Mb.just kin
    ∷ Mb.just kcolon  ∷ Mb.just kdot  ∷ Mb.just kassign
    ∷ Mb.just vxs     ∷ Mb.just vf    ∷ Mb.just vg     ∷ Mb.just vn
    ∷ Mb.just vx
    ∷ Mb.nothing
    ∷ []

------------------------------------------------------------------------
-- 2.  Phase one: the lexer, over `UChar`.
--
-- `which` reports the rule a lexeme matched; classifying by rule index is
-- the whole of the emission, since no rule of this lexicon has a payload.

emitTok : SemanticAction (ty ⟦ tokenRE lexicon ⟧) (Mb.Maybe Tok)
emitTok = semact-map (λ matched → tokenOfRule (matched .fst)) (which lexicon)

lexPhase : Phase (lv (tokensRE lexicon)) Tok
lexPhase = record
  { Ty = ty ⟦ tokensRE lexicon ⟧
  ; dec = lexer lexicon
  ; emit = semact-skip* emitTok
  }

lex : AS.String → Mb.Maybe (List Tok)
lex s = runPhase lexPhase (text s)

------------------------------------------------------------------------
-- 3.  The composite.
--
-- `Phase` gives no composition, so the join is metalanguage; keeping the
-- four failures apart is the point.  Each constructor carries what the
-- passes before it produced, so a failure says how far the front end got.

data Result : Type ℓ-zero where
  lexFail   : Result
  parseFail : List Tok → Result
  scopeFail : ATm → Result
  typeFail  : BTm → Result
  ok        : ATy → Result

pipeline : AS.String → Result
pipeline source = onLexed (lex source)
  where
  onTyped : BTm → Mb.Maybe ATy → Result
  onTyped scoped Mb.nothing = typeFail scoped
  onTyped scoped (Mb.just A) = ok A

  onScoped : List Tok → ATm → Mb.Maybe BTm → Result
  onScoped _ ast Mb.nothing = scopeFail ast
  onScoped toks _ (Mb.just scoped) = onTyped scoped (tyOf toks)

  onParsed : List Tok → Mb.Maybe ATm → Result
  onParsed toks Mb.nothing = parseFail toks
  onParsed toks (Mb.just ast) = onScoped toks ast (scopeOf toks)

  onLexed : Mb.Maybe (List Tok) → Result
  onLexed Mb.nothing = lexFail
  onLexed (Mb.just toks) = onParsed toks (astOf toks)

------------------------------------------------------------------------
-- 4.  Display.
--
-- The canonical readback, so a test states its expectation as the text a
-- reader would write rather than as an `ATy` constructor tree.

spaced : AS.String → AS.String → AS.String
spaced a b = AS.primStringAppend a (AS.primStringAppend " " b)

showTy : ATy → AS.String
showTy Bo = "bool"
showTy Na = "nat"
showTy (Ar A B) = AS.primStringAppend "arr " (spaced (showTy A) (showTy B))
showTy (Pr A B) = AS.primStringAppend "prod " (spaced (showTy A) (showTy B))
showTy (Li A) = AS.primStringAppend "list " (showTy A)


-- The front end's answer, as text: the inferred type, or which pass
-- refused.  This is what the test suite compares against.
report : Result → AS.String
report lexFail = "lex error"
report (parseFail _) = "parse error"
report (scopeFail _) = "scope error"
report (typeFail _) = "type error"
report (ok A) = showTy A

check : AS.String → AS.String
check source = report (pipeline source)
