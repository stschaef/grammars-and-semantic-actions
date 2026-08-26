{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- A one-sided Turing machine, and the type its accepting runs generate.

   `TuringTrace` is *not* a `μ` of a code: a move rewrites the tape rather
   than consuming input, so the recursion is not on the word.  What the DSL
   contributes is `Reify`: the trace is an ordinary predicate on strings, and
   `Reify` turns it into a type of the theory. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.FinSet
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Automata.Turing.OneSided.Base
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet)
  (isFinSetAlphabet : isFinSet Alphabet)
  where

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Nat
open import Cubical.Data.List using (List ; [] ; _∷_ ; rev)
open import Cubical.Data.Bool
import Cubical.Data.Sum as Sum
open import Cubical.Data.Empty as Empty hiding (rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Type.Reify.Base MonEqns Alphabet (λ _ → tt) listPresentation

private
  variable ℓT : Level

-- The tape alphabet adds a blank.
TapeAlphabet : Type ℓAlph
TapeAlphabet = Alphabet Sum.⊎ Unit

isSetTapeAlphabet : isSet TapeAlphabet
isSetTapeAlphabet = Sum.isSet⊎ isSetAlphabet isSetUnit

blank : TapeAlphabet
blank = Sum.inr tt

opaque
  isFinSetTapeAlphabet : isFinSet TapeAlphabet
  isFinSetTapeAlphabet =
    isFinSet⊎ (_ , isFinSetAlphabet) (Unit , isFinSetUnit)

data Shift : Type where
  L R : Shift

record TuringMachine ℓQ : Type (ℓ-suc (ℓ-max ℓQ ℓAlph)) where
  field
    Q : FinSet ℓQ
    init acc rej : ⟨ Q ⟩
    ¬acc≡rej : acc ≡ rej → Empty.⊥
    δ : ⟨ Q ⟩ → TapeAlphabet → ⟨ Q ⟩ × TapeAlphabet × Shift

  Tape : Type ℓAlph
  Tape = ∀ (n : ℕ) → TapeAlphabet

  Tape≡ : (t t' : Tape) → Type ℓAlph
  Tape≡ t t' = ∀ n → t n ≡ t' n

  consTape : TapeAlphabet → Tape → Tape
  consTape c tape zero = c
  consTape c tape (suc n) = tape n

  Head : Type ℓ-zero
  Head = ℕ

  writeTape : Tape → Head → TapeAlphabet → Tape
  writeTape tape head c m =
    decRec
      (λ _ → c)
      (λ _ → tape m)
      (discreteℕ head m)

  blankTape : Tape
  blankTape n = blank

  initHead : Head
  initHead = 0

  initTape : String → Tape
  initTape [] = blankTape
  initTape (c ∷ w) = consTape (Sum.inl c) (initTape w)

  mkTransition : ⟨ Q ⟩ → Tape → Head → ⟨ Q ⟩ → TapeAlphabet → Shift → ⟨ Q ⟩ × Tape × Head
  mkTransition q tape zero nextState toWrite L = nextState , writeTape tape zero toWrite , zero
  mkTransition q tape (suc head) nextState toWrite L = nextState , writeTape tape (suc head) toWrite , head
  mkTransition q tape zero nextState toWrite R = nextState , writeTape tape zero toWrite , suc zero
  mkTransition q tape (suc head) nextState toWrite R = nextState , writeTape tape (suc head) toWrite , suc (suc head)

  transition : ⟨ Q ⟩ → Tape → Head → ⟨ Q ⟩ × Tape × Head
  transition q tape head =
    let nextState , toWrite , dir = δ q (tape head) in
    mkTransition q tape head nextState toWrite dir

module _ {ℓQ} (TM : TuringMachine ℓQ) where
  open TuringMachine TM

  -- Non-linearly transition within the Turing Machine
  data TuringTrace (b : Bool) : ⟨ Q ⟩ × Tape × Head → Type (ℓ-max ℓQ ℓAlph) where
    accept : ∀ t h → b ≡ true → TuringTrace b (acc , t , h)
    reject : ∀ t h → b ≡ false → TuringTrace b (rej , t , h)
    move : ∀ q t h →
      TuringTrace b (transition q t h) →
      TuringTrace b (q , t , h)

  AcceptingFrom : ⟨ Q ⟩ × Tape × Head → Type (ℓ-max ℓQ ℓAlph)
  AcceptingFrom (q , t , h) = TuringTrace true (q , t , h)

  RejectingFrom : ⟨ Q ⟩ × Tape × Head → Type (ℓ-max ℓQ ℓAlph)
  RejectingFrom (q , t , h) = TuringTrace false (q , t , h)

  Accepting : String → Type (ℓ-max ℓQ ℓAlph)
  Accepting w = AcceptingFrom (init , initTape (rev w) , initHead)

  Rejecting : String → Type (ℓ-max ℓQ ℓAlph)
  Rejecting w = RejectingFrom (init , initTape (rev w) , initHead)

  -- A grammar that accepts a string if it is accepted by
  -- a Turing machine
  Turing : TheoryTy (ℓ-max ℓM (ℓ-max ℓQ ℓAlph)) tt
  Turing = Reify Accepting

