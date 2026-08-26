{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `a b*` again, but written as a regular *expression* and compiled.

   `RegExpExamples` builds the same automaton by hand out of `⊗Aut` and
   `*Aut`, discharging their side conditions inline.  Here the input is
   the syntax tree `＂ a ＂r ⊗r ＂ b ＂r *r` together with a `DetReg`
   derivation, and `compile` does the rest: the side conditions are
   `δq-fail`/`δᵢ-fail` at the subexpressions, not something the caller
   supplies.  What the caller does supply is the two `seq-unambig`
   arguments, and both are `Sum.inl tt*` because `litAut`'s follow-last
   set is everything.

   The resulting state set is `States (＂ a ＂r ⊗r ＂ b ＂r *r)`, which
   is `Unit* ⊎ Unit*` -- the two positions of the expression -- so this
   is the same automaton `RegExpExamples` built, reached from the
   syntax instead of from the constructions. -}
open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.Automaton.Implicit.CompileExamples where

open import Cubical.Data.Bool using (Bool ; true ; false)
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
open import Theory.Instances.Monoid.Automaton.Implicit.Compile L2 isSetAlphabet

------------------------------------------------------------------------
-- The syntax tree, and its determinism derivation.

private
  -- `litAut c` never steps once it has accepted, so every letter is
  -- outside its follow-last set and `⊤ℙ` is the honest index.
  anywhere : {P : ℙ} (c : L2) → (c ∈ℙ ⊤ℙ) Sum.⊎ (c ∈ℙ P)
  anywhere c = Sum.inl tt*

abStar-dr : DetReg _ (¬ℙ ⟦ a ⟧ℙ) true
abStar-dr = ＂ a ＂dr ⊗DR[ anywhere ] (＂ b ＂dr *DR[ anywhere ])

------------------------------------------------------------------------
-- Compiled.  `States abStar-dr` is `Unit* ⊎ Unit*`: one position per
-- literal, and nothing merged.  `erase` recovers the plain regular
-- literal, and nothing merged.

_ : States abStar-dr ≡ (Unit* Sum.⊎ Unit*)
_ = refl

DA : DeterministicAutomaton (FreelyAddFail+Initial (States abStar-dr))
DA = compileDA discL2 abStar-dr

open DeterministicAutomaton DA using (parseInit ; Trace ; init)

isSetQ : isSet (FreelyAddFail+Initial (States abStar-dr))
isSetQ = isSetCompileStates discL2 abStar-dr

------------------------------------------------------------------------
-- Running it.  As in `RegExpExamples`, `⊕[ b ] Trace b init` is total,
-- so the tests exhibit the run rather than comparing a `Bool`.

accepts : String → Bool
accepts w = parseInit isSetQ w (readChars w tt) .fst

traceOf : (w : String) → Trace (accepts w) init w
traceOf w = parseInit isSetQ w (readChars w tt) .snd

-- accepted
_ : Trace true init (a ∷ [])
_ = traceOf _

_ : Trace true init (a ∷ b ∷ b ∷ b ∷ [])
_ = traceOf _

-- rejected
_ : Trace false init []
_ = traceOf _

_ : Trace false init (b ∷ [])
_ = traceOf _

_ : Trace false init (a ∷ a ∷ [])
_ = traceOf _

_ : Trace false init (a ∷ b ∷ a ∷ [])
_ = traceOf _

------------------------------------------------------------------------
-- ...and at scale, to check that routing the side conditions through
-- `seqOf` did not put anything expensive on the transition path: the
-- proofs are scrutinised by `Sum.rec`, but `seq-unambig` answers
-- `Sum.inl` immediately and the proof itself is never forced.

bs : ℕ → String
bs zero = []
bs (suc n) = b ∷ bs n

_ : Trace true init (a ∷ bs 200)
_ = traceOf _

_ : Trace false init (a ∷ bs 200 ++ (a ∷ []))
_ = traceOf _
