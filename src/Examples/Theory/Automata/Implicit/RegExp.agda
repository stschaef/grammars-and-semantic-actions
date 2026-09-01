{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `a b*` over {a,b} via `Implicit/RegExp`'s constructions: no determinisation;
   side conditions discharged by `refl` since `litAut`'s follow set is empty. -}
open import Cubical.Foundations.Prelude

module Examples.Theory.Automata.Implicit.RegExp where

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Unit using (Unit* ; tt ; tt*)
open import Cubical.Relation.Nullary.Base using (Discrete ; yes ; no)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

data L2 : Type ℓ-zero where
  a b : L2

_≟L2_ : (x y : L2) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
a ≟L2 a = Sum.inl Eq.refl
b ≟L2 b = Sum.inl Eq.refl
a ≟L2 b = Sum.inr λ ()
b ≟L2 a = Sum.inr λ ()

discL2 : Discrete L2
discL2 a a = yes refl
discL2 b b = yes refl
discL2 a b = no λ p → Empty.rec (subst (λ where a → Unit* ; b → Empty.⊥) p tt*)
discL2 b a = no λ p → Empty.rec (subst (λ where b → Unit* ; a → Empty.⊥) p tt*)

open import Theory.Instances.Monoid.Types L2 _≟L2_
open import Theory.Instances.Monoid.KleeneStar L2 isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Deterministic L2 isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Implicit.RegExp L2 isSetAlphabet

open ImplicitDeterministicAutomaton

private
  -- `litAut` never steps after accepting: empty follow set, so every sequencing condition holds on the left
  litFollows : {c : L2} (d : L2)
    → ((q : Unit*) → litAut discL2 c .acc q ≡ true
         → fail ≡ litAut discL2 c .δq q d)
      Sum.⊎ (fail ≡ litAut discL2 c .δᵢ d)
  litFollows d = Sum.inl λ _ _ → refl

bStar : ImplicitDeterministicAutomaton (Unit* {ℓ-zero})
bStar = *Aut discL2 (litAut discL2 b) refl litFollows

abStar : ImplicitDeterministicAutomaton (Unit* {ℓ-zero} Sum.⊎ Unit* {ℓ-zero})
abStar = ⊗Aut discL2 (litAut discL2 a) bStar refl litFollows

DA : DeterministicAutomaton _
DA = IDA→DA abStar

DADead : Deadness DA
DADead = failDead abStar

isSetU : isSet (Unit* {ℓ-zero})
isSetU = isProp→isSet λ _ _ → refl

isSetQ : isSet _
isSetQ = isSetFreelyAddFail+Initial _ (Sum.isSet⊎ isSetU isSetU)

open DeterministicAutomaton DA using (parseInit ; Trace ; init)

-- `⊕[ b ] Trace b init` is total: the parse always returns a run and its
-- tag says whether it accepts; the tests exhibit the run itself.

accepts : String → Bool
accepts w = parseInit isSetQ w (readChars w tt) .fst

traceOf : (w : String) → Trace (accepts w) init w
traceOf w = parseInit isSetQ w (readChars w tt) .snd

_ : Trace true init (a ∷ [])
_ = traceOf _

_ : Trace true init (a ∷ b ∷ b ∷ b ∷ [])
_ = traceOf _

_ : Trace false init []
_ = traceOf _

_ : Trace false init (b ∷ [])
_ = traceOf _

_ : Trace false init (a ∷ a ∷ [])
_ = traceOf _

_ : Trace false init (a ∷ b ∷ a ∷ [])
_ = traceOf _

-- ...at scale, built at typechecking time.
--
-- Measured off-tree, against a 3.5s baseline (accept and reject
-- together, so roughly 2n characters per row):
--
--     n:     0    50   200   800  3200  12800  25600
--   sec:   3.5   3.1   3.5   3.6   5.2   13.8   26.7
--
-- ~0.45ms/char, and doubling the input from 12800 to 25600 costs 2.25x
-- the marginal time.  Linear.

bs : ℕ → String
bs zero = []
bs (suc n) = b ∷ bs n

_ : Trace true init (a ∷ bs 800)
_ = traceOf _

_ : Trace false init (a ∷ bs 800 ++ (a ∷ []))
_ = traceOf _
