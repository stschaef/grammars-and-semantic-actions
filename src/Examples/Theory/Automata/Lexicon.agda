{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Three-rule lexicon (keywords, identifiers, numbers, in priority order) — the two cases
   `Regex/Examples`' ordered choice gets wrong: "wherever" (longest match beats first match)
   and "where" (priority breaks the tie). -}
open import Cubical.Foundations.Prelude

module Examples.Theory.Automata.Lexicon where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
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

-- rules in priority order; nothing asks them to be disjoint, and they are not
module Rkw  = POSIX "where|let"
module Rid  = POSIX "[a-z][a-z0-9]*"
module Rnum = POSIX "[0-9]+"

Qs : Fin 3 → Type ℓ-zero
Qs fz = Rkw.Q
Qs (fs fz) = Rid.Q
Qs (fs (fs fz)) = Rnum.Q

Ms : (i : Fin 3) → DeterministicAutomaton (Qs i)
Ms fz = Rkw.DA
Ms (fs fz) = Rid.DA
Ms (fs (fs fz)) = Rnum.DA

Dead : (i : Fin 3) → Deadness (Ms i)
Dead fz = Rkw.Dead
Dead (fs fz) = Rid.Dead
Dead (fs (fs fz)) = Rnum.Dead

sQs : (i : Fin 3) → isSet (Qs i)
sQs fz = Rkw.isSetQ
sQs (fs fz) = Rid.isSetQ
sQs (fs (fs fz)) = Rnum.isSetQ

module Lx = Product Qs Ms Dead sQs

lexS : AS.String → Mb.Maybe (ℕ × AS.String)
lexS s = Mb.map-Maybe (λ x → toℕ (x .fst) , untext (x .snd .fst))
  (Lx.lexOneS (text s))

-- longest match beats first match
_ : lexS "wherever" ≡ Mb.just (1 , "wherever")
_ = refl

-- priority breaks the tie
_ : lexS "where" ≡ Mb.just (0 , "where")
_ = refl

-- ...and that really is a tie, not a keyword-only match
_ : Rkw.accepts (text "where") ≡ true
_ = refl

_ : Rid.accepts (text "where") ≡ true
_ = refl

-- ...while at "wherever" only the identifier rule is still alive
_ : Rkw.accepts (text "wherever") ≡ false
_ = refl

_ : Rid.accepts (text "wherever") ≡ true
_ = refl

_ : lexS "let" ≡ Mb.just (0 , "let")
_ = refl

_ : lexS "letter" ≡ Mb.just (1 , "letter")
_ = refl

_ : lexS "x9" ≡ Mb.just (1 , "x9")
_ = refl

_ : lexS "42" ≡ Mb.just (2 , "42")
_ = refl

_ : lexS "42x" ≡ Mb.just (2 , "42")
_ = refl

-- no token, not an empty one
_ : lexS "?" ≡ Mb.nothing
_ = refl

_ : lexS "" ≡ Mb.nothing
_ = refl

-- `scan` restarts at every token boundary (see note on `tokenise` in `Lexicon`), but the
-- restart costs the token, not the rest of the input: `scan-cons` exits at a dead state.
toks : AS.String → Mb.Maybe (List (ℕ × AS.String))
toks s = Mb.map-Maybe (L.map (λ x → toℕ (x .fst) , untext (x .snd)))
  (Lx.tokenise (text s))
  where import Cubical.Data.List as L

_ : toks "42where" ≡ Mb.just ((2 , "42") ∷ (0 , "where") ∷ [])
_ = refl

_ : toks "wherever42" ≡ Mb.just ((1 , "wherever42") ∷ [])
_ = refl

_ : toks "let42x" ≡ Mb.just ((1 , "let42x") ∷ [])
_ = refl

_ : toks "" ≡ Mb.just []
_ = refl

_ : toks "x?" ≡ Mb.nothing
_ = refl

-- Measured off-tree against the 3.2s baseline of this file:
--
--     n:    50   200   800  3200  12800
--   sec:  +0.1  +0.2  +0.7  +3.3  +17.5
--
-- Mild drift as in `Automaton/GreedyMaxExamples`, not squaring.  Only the 200 row is
-- checked here; `Automaton/Demo` carries the 3200 one, over five rules.

as : ℕ → List UChar
as zero = []
as (suc n) = ch 'a' ∷ as n

lexLen : List UChar → Mb.Maybe (ℕ × ℕ)
lexLen w = Mb.map-Maybe (λ x → toℕ (x .fst) , L.length (x .snd .fst))
  (Lx.lexOneS w)
  where import Cubical.Data.List as L

_ : lexLen (as 200 ++ (ch '?' ∷ [])) ≡ Mb.just (1 , 200)
_ = refl
