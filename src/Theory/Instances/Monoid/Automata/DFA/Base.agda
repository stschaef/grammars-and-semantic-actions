open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
module Theory.Instances.Monoid.Automata.DFA.Base
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.FinSet
open import Cubical.Data.Sigma

open import Theory.Instances.Monoid.Automaton.Deterministic
  Alphabet isSetAlphabet public

private variable ℓQ : Level

DFAOver : FinSet ℓQ → Type (ℓ-suc (ℓ-max ℓQ ℓAlph))
DFAOver Q = DeterministicAutomaton ⟨ Q ⟩

DFA : ∀ {ℓQ} → Type (ℓ-suc (ℓ-max ℓQ ℓAlph))
DFA {ℓQ} = Σ[ Q ∈ FinSet ℓQ ] DFAOver Q
