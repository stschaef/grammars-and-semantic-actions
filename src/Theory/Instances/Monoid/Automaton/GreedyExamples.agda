{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `Automaton/Greedy.scan`, run.  Nothing else exercises it
   computationally.

   The automaton is the `a b*` of `Implicit/RegExpExamples`.  On input
   `abbab` the longest accepted prefix is `abb` -- `a`, `ab` and `abb` all
   match, `abba` does not -- and `scan` finds it in one pass, with a
   refutation that nothing longer matches attached. -}
open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.Automaton.GreedyExamples where

open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.FinData using () renaming (zero to fz ; suc to fs)
import Cubical.Data.Sum as Sum

open import Theory.Instances.Monoid.Automaton.Implicit.RegExpExamples
open import Theory.Instances.Monoid.Types L2 _≟L2_
open import Theory.Instances.Monoid.KleeneStar L2 isSetAlphabet using (readChars)
open import Theory.Instances.Monoid.Automaton.Deterministic L2 isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Greedy L2 isSetAlphabet

open DeterministicAutomaton DA using (init)

munch : String → String
munch w =
  Sum.rec (λ x → x .snd .fst fz) (λ _ → [])
    (scan DA isSetQ w (readChars w tt) init)

_ : munch (a ∷ b ∷ b ∷ a ∷ b ∷ []) ≡ a ∷ b ∷ b ∷ []
_ = refl

_ : munch (a ∷ b ∷ []) ≡ a ∷ b ∷ []
_ = refl

_ : munch (a ∷ []) ≡ a ∷ []
_ = refl

_ : munch (b ∷ b ∷ []) ≡ []
_ = refl
