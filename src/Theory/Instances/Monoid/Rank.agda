{- The free-monoid order used by guarded recursive descent: a recursive
   parser may only be queried after a token has been consumed.  On the list
   presentation the monoid's rank is literally the list length. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Rank
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Categories.Direct.Base using (WFOrder)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.WFOrder using (ℕWF)
open import Cubical.Data.Sigma using (snd)
open import Cubical.Data.Unit using (tt ; isSetUnit)
import Cubical.Data.List as L

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.ListPresentation Alphabet isSetAlphabet
  using (listPresentation)
open import Theory.Base MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Guarded.Base MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Guarded.Justification MonEqns Alphabet (λ _ → tt)
  listPresentation

String : Type ℓM
String = ↓M tt

length : String → ℕ
length = L.length

Fam : (ℓA : Level) → Type _
Fam ℓA = (s : Sorts) → TheoryTy ℓA s

-- The monoid world's step relation: a recursive call is entitled to a
-- shorter input.  This is the only place `length` appears in a type.
Shorter : Pt {X = Sorts} (λ s → s) → Pt (λ s → s) → Type ℓ-zero
Shorter p q = WFOrder._<_ ℕWF (length (p .snd)) (length (q .snd))

module Guarded▷ {ℓA} (A : Fam ℓA) (isSetA : ∀ s m → isSet (A s m)) where
  private
    monoidLöb : Löb Shorter A
    monoidLöb = löbByMeasure {X = Sorts} {xs = λ s → s}
      isSetUnit ℕWF (λ p → length (p .snd)) (λ r → r) A isSetA

  open Löb monoidLöb public
