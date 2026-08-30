{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Maximal munch over the scan whose type SAYS the match is maximal.
   The automaton is `a b*`; the end state is forced by `TraceTo` rather
   than existentially guessed, and extending is a `STEP` rather than an
   `extendAt` with its transport. -}
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

_ : munch (a ∷ b ∷ []) ≡ a ∷ b ∷ []
_ = refl

_ : munch (a ∷ []) ≡ a ∷ []
_ = refl

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

-- At scale: the scan is linear in the input.

_ : munch (a ∷ bs 200 ++ (a ∷ b ∷ [])) ≡ a ∷ bs 200
_ = refl

_ : munch (a ∷ bs 3200 ++ (a ∷ b ∷ [])) ≡ a ∷ bs 3200
_ = refl
