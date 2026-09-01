{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Maximal munch for `a b*`; `TraceTo` forces the end state rather than
   guessing it.  Supersedes the `GreedyAt` version the inline timings are
   compared against. -}
open import Cubical.Foundations.Prelude

module Examples.Theory.Automata.GreedyMax where

open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.FinData using () renaming (zero to fz ; suc to fs)
import Cubical.Data.Sum as Sum

open import Examples.Theory.Automata.Implicit.RegExp
open import Theory.Instances.Monoid.Types L2 _≟L2_
open import Theory.Instances.Monoid.KleeneStar L2 isSetAlphabet using (readChars)
open import Theory.Instances.Monoid.Automaton.Deterministic L2 isSetAlphabet
open import Theory.Instances.Monoid.Automaton.GreedyMax L2 isSetAlphabet

open DeterministicAutomaton DA using (init)

munch : String → String
munch w =
  Sum.rec (λ x → x .snd .fst fz) (λ _ → [])
    (scan DA isSetQ DADead w (readChars w tt) init)

munchEnd : String → Sum._⊎_ _ _
munchEnd w =
  Sum.rec (λ x → Sum.inl (x .fst)) (λ _ → Sum.inr tt)
    (scan DA isSetQ DADead w (readChars w tt) init)

_ : munch (a ∷ b ∷ b ∷ a ∷ b ∷ []) ≡ a ∷ b ∷ b ∷ []
_ = refl

-- maximal: does not stop at the first accepting state, which would give "a"
_ : munch (a ∷ b ∷ []) ≡ a ∷ b ∷ []
_ = refl

_ : munch (a ∷ []) ≡ a ∷ []
_ = refl

-- no match, not ε
_ : munch (b ∷ b ∷ []) ≡ []
_ = refl

-- the same match via the word-indexed certificate `Run→Greedy`
munchSpec : String → String
munchSpec w =
  Sum.rec (λ x → x .fst) (λ _ → [])
    (Run→Greedy DA init w (scan DA isSetQ DADead w (readChars w tt) init))

_ : munchSpec (a ∷ b ∷ b ∷ a ∷ b ∷ []) ≡ a ∷ b ∷ b ∷ []
_ = refl

_ : munchSpec (b ∷ b ∷ []) ≡ []
_ = refl

-- At scale, measured off-tree against a 3.0s baseline (empty module
-- importing this one), same machine as the `GreedyExamples` table:
--
--     n:     0   200   800  3200  12800  51200
--   sec:   3.0   3.1   3.3   4.8    9.9   49.8
--
-- Same shape as the unproved `GreedyAt` scan (0/200/800/3200/12800 =
-- 2.9/3.0/3.4/5.1/12.3), slightly faster: extending is one `STEP`, where
-- `extendAt` went through `Dl` and a transport.

_ : munch (a ∷ bs 200 ++ (a ∷ b ∷ [])) ≡ a ∷ bs 200
_ = refl

_ : munch (a ∷ bs 3200 ++ (a ∷ b ∷ [])) ≡ a ∷ bs 3200
_ = refl
