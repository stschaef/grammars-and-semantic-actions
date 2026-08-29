{-# OPTIONS --lossy-unification #-}
{- What the generic development buys back.

   `Semantics.Distributivity` derives distributivity of ⊗ over ⊕ᴰ from
   nothing but the fact that ⊗ is biclosed. `Grammar.Sum.Properties`
   proves the same statement by hand, by unfolding ⊗ into a sigma of
   splittings.

   Instantiating the generic proof at the families model gives a term
   of literally the same type as the hand-written one — and the two
   agree, provably, from the β laws on both sides.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Instances.Recovered (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure using (⟨_⟩)

import Grammar.Sum.Properties Alphabet as SumP
open import Grammar.Equivalence.Base Alphabet using (StrongEquivalence)

open import Semantics.Instances.Families Alphabet
open import Semantics.Notation Literals
open import Semantics.Distributivity Literals

open StrongEquivalence

module _ {X : hSet ℓ-zero} {A : ⟨ X ⟩ → Grammar} {B : Grammar} where

  -- The two constructions of the distributor are the same map.
  distL-agrees :
    ⊕ᴰ-distL {X = X} {A = A} {B = B}
      ≡ SumP.⊕ᴰ-distL {X = ⟨ X ⟩} {A = B .fst} {B = λ x → A x .fst} .fun
  distL-agrees = ⊗ᴰ≡ λ x → ⊕ᴰ-distL-β x ∙ sym SumP.⊕ᴰ-distL-β

  distR-agrees :
    ⊕ᴰ-distR {X = X} {A = A} {B = B}
      ≡ SumP.⊕ᴰ-distR {X = ⟨ X ⟩} {A = B .fst} {B = λ x → A x .fst} .fun
  distR-agrees = ᴰ⊗≡ λ x → ⊕ᴰ-distR-β x ∙ sym SumP.⊕ᴰ-distR-β
