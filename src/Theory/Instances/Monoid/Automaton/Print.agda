{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Reading a run back out as its input word.  `parse` and `print` are two
   folds over the same inductive structure -- `char *` one way, the trace
   the other -- so their composite is the run's uniqueness rather than a
   separate induction.  Both directions come from a proposition: `char *`
   is one (`KleeneStar/Read`), and so is `Runs q` (`Automaton/Disjoint`). -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Automaton.Print
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar.Read Alphabet isSetAlphabet
  using (unambiguous-char*)
open import Theory.Instances.Monoid.Convolution Alphabet isSetAlphabet
  using (⟦⊗e⟧⁻ ; ⊗e-ε←)
open import Theory.Instances.Monoid.Automaton.Deterministic
  Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Disjoint
  Alphabet isSetAlphabet using (Runs ; unambiguous-Runs)

private variable ℓQ : Level

module _ {Q : Type ℓQ} (Aut : DeterministicAutomaton Q) where
  open DeterministicAutomaton Aut

  printAlg : (b : Bool) → TraceAlg b (λ _ → char *)
  printAlg b (lift q) = ⊕ᴰ-elim λ where
    (stop _) → roll ∘⊢ σ⊕ false ∘⊢ ⊗e-ε← _ ∘⊢ lowerTy
    (step c) → roll ∘⊢ σ⊕ true ∘⊢ ⟦⊗e⟧⁻ _ _
      ∘⊢ ⊗-map (liftTy ∘⊢ σ⊕ c) liftTy ∘⊢ step-out c

  print : (b : Bool) (q : Q) → Trace b q ⊢ char *
  print b q = rec (TraceTy b) (printAlg b) (lift q)

  -- `char *` is a proposition, so `print` is the only map a run has into it.
  print-unique : (b : Bool) (q : Q) (f : Trace b q ⊢ char *) → f ≡ print b q
  print-unique b q f =
    funExt λ m → funExt λ t → unambiguous-char* m (f m t) (print b q m t)

  -- ...and re-parsing a printed run returns it: both sides are maps into
  -- `Runs q`, which is a proposition.
  module _ (isSetQ : isSet Q) where
    private
      reparse : (b : Bool) (q : Q) → Trace b q ⊢ Runs Aut q
      reparse b q = π {A = Runs Aut} q ∘⊢ parse isSetQ ∘⊢ print b q

    parse-print : (b : Bool) (q : Q) → reparse b q ≡ σ⊕ b
    parse-print b q =
      funExt λ m → funExt λ t →
        unambiguous-Runs Aut q m (reparse b q m t) (b , t)
