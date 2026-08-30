{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A three-rule lexicon, run.

   Keywords, identifiers and numbers, in that priority order.  The two
   properties a lexicon has to have are exactly the two cases the
   ordered-choice lexer of `Regex/Examples` gets wrong:

     "wherever" -- longest match beats first match: the keyword rule
                   matches a prefix, the identifier rule matches more,
                   so the identifier wins.
     "where"    -- priority breaks a tie: both rules match all five
                   characters, and the keyword rule is earlier. -}
open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.Automaton.LexiconExamples where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.FinData using (Fin ; toℕ) renaming (zero to fz ; suc to fs)
import Cubical.Data.Maybe as Mb
import Agda.Builtin.String as AS

open import Theory.Instances.Monoid.Regex.Parse
open import Theory.Instances.Monoid.Automaton.Deterministic UChar isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Implicit.AnalysisExamples
  using (module POSIX)
open import Theory.Instances.Monoid.Automaton.Lexicon UChar isSetAlphabet

-- The rules, in priority order.  Each is compiled on its own; nothing
-- asks the three of them to be disjoint, and they are not.

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

-- Longest match beats first match: `where` matches a prefix, the
-- identifier rule matches all of it.
_ : lexS "wherever" ≡ Mb.just (1 , "wherever")
_ = refl

_ : lexS "where" ≡ Mb.just (0 , "where")
_ = refl

_ : Rkw.endsAccepting (text "where") ≡ true
_ = refl

_ : Rid.endsAccepting (text "where") ≡ true
_ = refl

_ : Rkw.endsAccepting (text "wherever") ≡ false
_ = refl

_ : Rid.endsAccepting (text "wherever") ≡ true
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

_ : lexS "?" ≡ Mb.nothing
_ = refl

_ : lexS "" ≡ Mb.nothing
_ = refl

-- The tokenising loop.  `scan` is restarted at every token boundary --
-- see the note on `tokenise` in `Lexicon` -- but the restart now costs
-- the token rather than the rest of the input: `GreedyMax.scan-cons`
-- exits at a dead product state.

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

-- At length: three automata step in lockstep, and the scan is still one
-- pass, not the squaring that re-deriving the match would give.

as : ℕ → List UChar
as zero = []
as (suc n) = ch 'a' ∷ as n

lexLen : List UChar → Mb.Maybe (ℕ × ℕ)
lexLen w = Mb.map-Maybe (λ x → toℕ (x .fst) , L.length (x .snd .fst))
  (Lx.lexOneS w)
  where import Cubical.Data.List as L

_ : lexLen (as 200 ++ (ch '?' ∷ [])) ≡ Mb.just (1 , 200)
_ = refl
