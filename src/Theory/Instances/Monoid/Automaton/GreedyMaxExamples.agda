{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Maximal munch over the scan whose type SAYS the match is maximal.
   The automaton is `a b*`; the end state is forced by `TraceTo` rather
   than existentially guessed, and extending is a `STEP` rather than an
   `extendAt` with its transport.  This supersedes the `GreedyAt` version
   these numbers used to be compared against, which is why the older
   timings appear inline below. -}
open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.Automaton.GreedyMaxExamples where

open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.FinData using () renaming (zero to fz ; suc to fs)
import Cubical.Data.Sum as Sum

open import Theory.Instances.Monoid.Automaton.Implicit.RegExpExamples
open import Theory.Instances.Monoid.Types L2 _≟L2_
open import Theory.Instances.Monoid.KleeneStar L2 isSetAlphabet using (readChars)
open import Theory.Instances.Monoid.Automaton.Deterministic L2 isSetAlphabet
open import Theory.Instances.Monoid.Automaton.GreedyMax L2 isSetAlphabet

open DeterministicAutomaton DA using (init)

-- the matched prefix: the left factor of the greedy witness' splitting
munch : String → String
munch w =
  Sum.rec (λ x → x .snd .fst fz) (λ _ → [])
    (scan DA isSetQ DADead w (readChars w tt) init)

-- ...and the state it ended in, which the type now pins down
munchEnd : String → Sum._⊎_ _ _
munchEnd w =
  Sum.rec (λ x → Sum.inl (x .fst)) (λ _ → Sum.inr tt)
    (scan DA isSetQ DADead w (readChars w tt) init)

-- `a b*` on "abbab": the longest accepted prefix is "abb"
_ : munch (a ∷ b ∷ b ∷ a ∷ b ∷ []) ≡ a ∷ b ∷ b ∷ []
_ = refl

-- ...and it really is *maximal*: it does not stop at the first accepting
-- state, which would give "a"
_ : munch (a ∷ b ∷ []) ≡ a ∷ b ∷ []
_ = refl

_ : munch (a ∷ []) ≡ a ∷ []
_ = refl

-- nothing accepts here, so the scan reports no match rather than ε
_ : munch (b ∷ b ∷ []) ≡ []
_ = refl

-- the same match read off the *word-indexed* certificate: `Run→Greedy`
-- turns the cheap state-indexed witness into `Greedy (L init)`, whose
-- `⊕[ w ]` index is literally the matched word.
munchSpec : String → String
munchSpec w =
  Sum.rec (λ x → x .fst) (λ _ → [])
    (Run→Greedy DA init w (scan DA isSetQ DADead w (readChars w tt) init))

_ : munchSpec (a ∷ b ∷ b ∷ a ∷ b ∷ []) ≡ a ∷ b ∷ b ∷ []
_ = refl

_ : munchSpec (b ∷ b ∷ []) ≡ []
_ = refl

-- ...at scale.  Measured off-tree against a 3.0s baseline (an empty
-- module importing this one), on the same machine as the table in
-- `GreedyExamples`:
--
--     n:     0   200   800  3200  12800  51200
--   sec:   3.0   3.1   3.3   4.8    9.9   49.8
--
-- i.e. the same shape as the unproved `GreedyAt` scan (0/200/800/3200/
-- 12800 = 2.9/3.0/3.4/5.1/12.3), slightly faster: extending a match is now
-- a single `STEP`, where `extendAt` went through `Dl` and a transport.

_ : munch (a ∷ bs 200 ++ (a ∷ b ∷ [])) ≡ a ∷ bs 200
_ = refl

_ : munch (a ∷ bs 3200 ++ (a ∷ b ∷ [])) ≡ a ∷ bs 3200
_ = refl
