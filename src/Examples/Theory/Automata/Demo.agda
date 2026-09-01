{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- POSIX regex lexer demo: five rules run in lockstep as a product; longest
   match wins, earliest rule breaks ties.  Every `_ = refl` runs at
   typechecking time. -}
open import Cubical.Foundations.Prelude

module Examples.Theory.Automata.Demo where

open import Cubical.Data.Nat as N using (ℕ)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.FinData using (Fin ; toℕ) renaming (zero to fz ; suc to fs)
import Cubical.Data.Maybe as Mb
import Agda.Builtin.String as AS

open import Cubical.Data.Unicode
open import Theory.Instances.Monoid.Regex.Parse
open import Theory.Instances.Monoid.Automaton.Deterministic UChar isSetUChar
open import Examples.Theory.Automata.Implicit.Analysis
  using (module POSIX)
open import Theory.Instances.Monoid.Automaton.Lexicon UChar isSetUChar

-- 1. Rules, POSIX source, priority order.  Deliberately overlapping:
-- resolved by longest match then priority, not disjointness.

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

module Lex = Product Qs Ms Dead sQs

lex : AS.String → Mb.Maybe (ℕ × AS.String)
lex s = Mb.map-Maybe (λ x → toℕ (x .fst) , untext (x .snd .fst))
  (Lex.lexOneS (text s))

-- 2. Rule 0 keyword, 1 identifier, 2 number, 3 operator, 4 whitespace.

-- greedy: never stops at the first accepting position
_ : lex "1234"     ≡ Mb.just (2 , "1234")
_ = refl

_ : lex "+++"      ≡ Mb.just (3 , "+++")
_ = refl

_ : lex "counter7" ≡ Mb.just (1 , "counter7")
_ = refl

-- stops where the rule stops, not at end of input
_ : lex "42abc"    ≡ Mb.just (2 , "42")
_ = refl

_ : lex "abc42+"   ≡ Mb.just (1 , "abc42")
_ = refl

_ : lex "  x"      ≡ Mb.just (4 , "  ")
_ = refl

-- longest match beats priority: rule 0 matches five chars, rule 1 all eight
_ : lex "wherever" ≡ Mb.just (1 , "wherever")
_ = refl

-- priority breaks the tie: both match five, rule 0 is earlier
_ : lex "where"    ≡ Mb.just (0 , "where")
_ = refl

_ : lex "let"      ≡ Mb.just (0 , "let")
_ = refl

_ : lex "letter"   ≡ Mb.just (1 , "letter")
_ = refl

-- a refutation, not a failure to find a match
_ : lex "?"        ≡ Mb.nothing
_ = refl

_ : lex ""         ≡ Mb.nothing
_ = refl

-- 3. At scale: five automata in lockstep.  Timings measured off-tree vs a
-- baseline building all five rules but lexing nothing; 4x input = 4x time.

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
