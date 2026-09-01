{- DRAFT — deliberately left open; the precise statement is not settled.

   A printer for a phase should satisfy a roundtrip law.  Two candidate
   statements; which is right (or whether print should be *derived* from
   the emitter's fibers rather than supplied) is the open design choice:

   1. reparse:  observe dec (semact-dec emit) ∘ print ≡ just
      -- printed output parses back to the same value
   2. canonical: print ∘ (observe dec (semact-dec emit)) ⊑ id on accepted
      input -- printing a parse yields a canonical form of the input

   `Automaton/Print.parse-print` is (1) at the deterministic-automaton
   level; nothing yet states either at the semantic-action level. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Phase.Roundtrip
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Maybe using (Maybe ; just)
open import Cubical.Data.List using (List)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Phase Alphabet isSetAlphabet

private variable ℓA ℓO : Level

record PrintablePhase (ℓA : Level) (Out : Type ℓO)
  : Type (ℓ-max (ℓ-suc (ℓ-max ℓA ℓO)) (ℓ-max ℓM ℓAlph)) where
  field
    phase : Phase ℓA Out
    print : List Out → String
    reparse : (xs : List Out) → runPhase phase (print xs) ≡ just xs
