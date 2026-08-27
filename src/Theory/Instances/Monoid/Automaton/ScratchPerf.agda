{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.Automaton.ScratchPerf where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; length)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.FinData using (Fin ; toℕ) renaming (zero to fz ; suc to fs)
import Cubical.Data.Maybe as Mb
import Cubical.Data.Sum as Sum

open import Theory.Instances.Monoid.Regex.Parse
open import Theory.Instances.Monoid.Automaton.Deterministic UChar isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Implicit.AnalysisExamples
  using (module POSIX)
open import Theory.Instances.Monoid.Automaton.Lexicon UChar isSetAlphabet
import Theory.Instances.Monoid.Automaton.Greedy as G

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

as : ℕ → List UChar
as zero = []
as (suc n) = ch 'a' ∷ as n

-- OLD path: Greedy's scan, projecting the splitting by hand
oldScan = G.scan UChar isSetAlphabet Lx.Prod Lx.isSetProdQ

-- BENCH 473108713

E6 : List UChar → Mb.Maybe (Fin 3)
E6 w = Sum.rec (λ t → Lx.winner (t .fst)) (λ _ → Mb.nothing)
  (Lx.lexOne w (Lx.runInit w tt))

_ : E6 (as 3200 ++ (ch '?' ∷ [])) ≡ Mb.just (fs fz)
_ = refl

