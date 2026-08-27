{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- POSIX regexes, parsed greedily, at scale.

   Five rules written as POSIX source strings.  Each is parsed by the
   POSIX front end, analysed into a deterministic regex, compiled to an
   automaton, and run; the five run in lockstep as a product, so one
   pass finds the longest match across all of them and the earliest rule
   wins a tie.

   Every `_ = refl` below is the parser actually running at typechecking
   time -- these are computations, not assertions about computations.

   Read the table as: input text on the left, and on the right which
   rule won and exactly what it consumed. -}
open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.Automaton.Demo where

open import Cubical.Data.Nat as N using (ℕ)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.FinData using (Fin ; toℕ) renaming (zero to fz ; suc to fs)
import Cubical.Data.Maybe as Mb
import Agda.Builtin.String as AS

open import Theory.Instances.Monoid.Unicode.Base
open import Theory.Instances.Monoid.Regex.Parse
open import Theory.Instances.Monoid.Automaton.Deterministic UChar isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Implicit.AnalysisExamples
  using (module POSIX)
open import Theory.Instances.Monoid.Automaton.Lexicon UChar isSetAlphabet

------------------------------------------------------------------------
-- 1. The rules, as POSIX source, in priority order.
--
-- Nothing asks these five to be disjoint, and they are not: `where`
-- matches rule 0 and rule 1 both, and every keyword is also a legal
-- identifier.  That is the point -- overlap is resolved by longest
-- match first and priority second, not by a disjointness side
-- condition.

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

sQs : (i : Fin 5) → isSet (Qs i)
sQs fz = Kw.isSetQ
sQs (fs fz) = Ident.isSetQ
sQs (fs (fs fz)) = Num.isSetQ
sQs (fs (fs (fs fz))) = Op.isSetQ
sQs (fs (fs (fs (fs fz)))) = Space.isSetQ

module Lex = Product Qs Ms sQs

-- rule index and matched text, as text
lex : AS.String → Mb.Maybe (ℕ × AS.String)
lex s = Mb.map-Maybe (λ x → toℕ (x .fst) , untext (x .snd .fst))
  (Lex.lexOneS (text s))

------------------------------------------------------------------------
-- 2. The table.  Rule 0 keyword, 1 identifier, 2 number, 3 operator,
--    4 whitespace.

-- Greedy: the match runs as far as it can, never stopping at the first
-- accepting position.
_ : lex "1234"     ≡ Mb.just (2 , "1234")
_ = refl

_ : lex "+++"      ≡ Mb.just (3 , "+++")
_ = refl

_ : lex "counter7" ≡ Mb.just (1 , "counter7")
_ = refl

-- ...and it stops exactly where the rule stops, not at the end of input
_ : lex "42abc"    ≡ Mb.just (2 , "42")
_ = refl

_ : lex "abc42+"   ≡ Mb.just (1 , "abc42")
_ = refl

_ : lex "  x"      ≡ Mb.just (4 , "  ")
_ = refl

-- Longest match beats priority: `where` is rule 0 and matches five
-- characters, but rule 1 matches all eight, so rule 1 wins.
_ : lex "wherever" ≡ Mb.just (1 , "wherever")
_ = refl

-- Priority beats a tie: here both rules match exactly five, and rule 0
-- is earlier.
_ : lex "where"    ≡ Mb.just (0 , "where")
_ = refl

_ : lex "let"      ≡ Mb.just (0 , "let")
_ = refl

_ : lex "letter"   ≡ Mb.just (1 , "letter")
_ = refl

-- No rule matches, and that is a refutation rather than a failure to
-- find one.
_ : lex "?"        ≡ Mb.nothing
_ = refl

_ : lex ""         ≡ Mb.nothing
_ = refl

------------------------------------------------------------------------
-- 3. At scale.
--
-- Five automata in lockstep over a long identifier.  Timings measured
-- off-tree against a baseline that builds all five rules but lexes
-- nothing; 4x the input costs 4x the time.

xs : ℕ → List UChar
xs N.zero = []
xs (N.suc j) = ch 'x' ∷ xs j

len : Mb.Maybe (Fin 5 × String × String) → ℕ
len Mb.nothing = 0
len (Mb.just x) = length (x .snd .fst)
  where open import Cubical.Data.List using (length)

-- a 3200-character identifier, matched in one pass
_ : len (Lex.lexOneS (xs 3200 ++ (ch '?' ∷ []))) ≡ 3200
_ = refl
