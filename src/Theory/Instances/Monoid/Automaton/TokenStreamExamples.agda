{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The token stream, run.

   `Automaton/Demo` runs `lexOne`: one token, with a `Maybe` at the
   boundary.  Here the same five POSIX rules are run as `Stream`, whose
   `Decidable` is a `⊢`-term and whose parse tree *is* the token list.

   Every `_ = refl` is the decision computing at typechecking time. -}
open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.Automaton.TokenStreamExamples where

open import Cubical.Data.Nat as N using (ℕ)
open import Cubical.Data.Bool using (false)
open import Cubical.Data.List using (List ; [] ; _∷_)
import Cubical.Data.List as L
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.FinData using (Fin ; toℕ) renaming (zero to fz ; suc to fs)
import Cubical.Data.Maybe as Mb
import Cubical.Data.Equality as Eq
import Agda.Builtin.String as AS

open import Theory.Instances.Monoid.Unicode.Base
open import Theory.Instances.Monoid.Regex.Parse
open import Theory.Instances.Monoid.Automaton.Deterministic UChar isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Implicit.AnalysisExamples
  using (module POSIX)
open import Theory.Instances.Monoid.Automaton.TokenStream UChar isSetAlphabet
  using (module Stream)
open import Theory.Instances.Monoid.Phase UChar isSetAlphabet using (runPhase)

open DeterministicAutomaton

-- The same five rules as `Automaton/Demo`, in priority order.

module Kw    = POSIX "let|in|where"
module Ident = POSIX "[a-z][a-z0-9]*"
module Num   = POSIX "[0-9]+"
module Op    = POSIX "[-+*/=<>]+"
module Space = POSIX "[ \t\n]+"

Qs : Fin 5 → Type ℓ-zero
Qs fz = Kw.Q
Qs (fs fz) = Ident.Q
Qs (fs (fs fz)) = Num.Q
Qs (fs (fs (fs fz))) = Op.Q
Qs (fs (fs (fs (fs fz)))) = Space.Q

Ms : (i : Fin 5) → DeterministicAutomaton (Qs i)
Ms fz = Kw.DA
Ms (fs fz) = Ident.DA
Ms (fs (fs fz)) = Num.DA
Ms (fs (fs (fs fz))) = Op.DA
Ms (fs (fs (fs (fs fz)))) = Space.DA

Dead : (i : Fin 5) → Deadness (Ms i)
Dead fz = Kw.Dead
Dead (fs fz) = Ident.Dead
Dead (fs (fs fz)) = Num.Dead
Dead (fs (fs (fs fz))) = Op.Dead
Dead (fs (fs (fs (fs fz)))) = Space.Dead

sQs : (i : Fin 5) → isSet (Qs i)
sQs fz = Kw.isSetQ
sQs (fs fz) = Ident.isSetQ
sQs (fs (fs fz)) = Num.isSetQ
sQs (fs (fs (fs fz))) = Op.isSetQ
sQs (fs (fs (fs (fs fz)))) = Space.isSetQ

module Lex = Stream Qs Ms Dead sQs

-- The side condition of the stream: no rule of this lexicon accepts the
-- empty word, so every token consumes and the recursion descends.  It is
-- a computation, not an assumption.
noNullRule : isAcc Lex.Prod (init Lex.Prod) Eq.≡ false
noNullRule = Eq.refl

-- rule indices and lexemes, as text
toks : AS.String → Mb.Maybe (List (ℕ × AS.String))
toks s = Mb.map-Maybe (L.map (λ x → toℕ (x .fst) , untext (x .snd)))
  (Lex.tokeniseS noNullRule (text s))

-- one token, the way `Demo` reads it
lex1 : AS.String → Mb.Maybe (ℕ × AS.String)
lex1 s = Mb.map-Maybe (λ x → toℕ (x .fst) , untext (x .snd .fst))
  (Lex.lexOneS (text s))

-- 1. The `wherever`/`where` pair comes out the same through the stream
--    as through `lexOne`: longest match beats priority, priority beats a
--    tie, and the stream adds only that nothing is left over.

_ : lex1 "wherever" ≡ Mb.just (1 , "wherever")
_ = refl

_ : toks "wherever" ≡ Mb.just ((1 , "wherever") ∷ [])
_ = refl

_ : lex1 "where" ≡ Mb.just (0 , "where")
_ = refl

_ : toks "where" ≡ Mb.just ((0 , "where") ∷ [])
_ = refl

-- 2. Several tokens, which `lexOne` cannot say anything about.

_ : toks "let x42"
  ≡ Mb.just ((0 , "let") ∷ (4 , " ") ∷ (1 , "x42") ∷ [])
_ = refl

_ : toks "1+2"
  ≡ Mb.just ((2 , "1") ∷ (3 , "+") ∷ (2 , "2") ∷ [])
_ = refl

-- 3. The empty word is a stream -- the `nil` summand -- and a word with
--    no lexing is refuted rather than dropped.

_ : toks "" ≡ Mb.just []
_ = refl

_ : toks "?" ≡ Mb.nothing
_ = refl

-- ...including when the failure is in the middle: `let ?` lexes two
-- tokens and then cannot continue, and the whole word is refuted.
_ : toks "let ?" ≡ Mb.nothing
_ = refl

-- 4. The same thing as a `Phase`: `runPhase` is `observe` of the phase's
--    own decision and emission, so the greedy lexer now fits the
--    interface that `dec : Decidable Gr` used to exclude.

phaseToks : AS.String → Mb.Maybe (List (ℕ × AS.String))
phaseToks s = Mb.map-Maybe (L.map (λ x → toℕ (x .fst) , untext (x .snd)))
  (runPhase (Lex.lexPhase noNullRule) (text s))

_ : phaseToks "let x42"
  ≡ Mb.just ((0 , "let") ∷ (4 , " ") ∷ (1 , "x42") ∷ [])
_ = refl

_ : phaseToks "?" ≡ Mb.nothing
_ = refl

-- 5. At scale: 19 tokens in one pass.
_ : Mb.map-Maybe L.length
      (Lex.tokeniseS noNullRule (text "let x1 = y2 + 33 in where wherever z"))
  ≡ Mb.just 19
_ = refl
