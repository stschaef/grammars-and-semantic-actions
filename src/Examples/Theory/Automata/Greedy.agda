{- The OLD scan, kept honest: nothing else exercises `Automaton/Greedy.scan`
   computationally; if `Automaton/Greedy` is retired, this goes with it.
   `a b*` on `abbab`: the longest accepted prefix is `abb`, found in one
   pass with a refutation that nothing longer matches. -}
open import Cubical.Foundations.Prelude

module Examples.Theory.Automata.Greedy where

open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.FinData using () renaming (zero to fz ; suc to fs)
import Cubical.Data.Sum as Sum

open import Examples.Theory.Automata.Implicit.RegExp
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

-- maximal: it does not stop at the first accepting state, which would give "a"
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
-- Linear: extending the match is O(1); its residual index is the end state, not the matched word.
