{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Maximal munch, run.

   The automaton is the `a b*` of `Implicit/RegExpExamples`.  On input
   `abbab` the longest accepted prefix is `abb` -- `a`, `ab` and `abb`
   all match, `abba` does not -- and `scan` finds it in one pass, with a
   refutation that nothing longer matches attached.

   The greedy witness carries the state its match ended in, so extending
   a match costs an associativity and a substitution rather than a
   rebuild of the matched word. -}
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

-- The greedy scan over that automaton.

munch : String → String
munch w =
  Sum.rec (λ x → x .snd .fst fz) (λ _ → [])
    (scan DA isSetQ w (readChars w tt) init)

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

-- ...at scale.  Measured off-tree against a ~2.9s baseline:
--
--     n:     0    50   200   800  3200  12800
--   sec:   2.9   3.0   3.0   3.4   5.1   12.3
--
-- Linear: the recursive call is made once per character and consulted
-- at each state, and extending the match is O(1) because its residual
-- index is the end state rather than the matched word.

_ : munch (a ∷ bs 200 ++ (a ∷ b ∷ [])) ≡ a ∷ bs 200
_ = refl
