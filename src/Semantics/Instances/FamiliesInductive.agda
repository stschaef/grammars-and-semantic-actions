{-# OPTIONS --lossy-unification #-}
{- Relating the model-generic functor codes to `Grammar.Inductive`.

   `Semantics.Inductive.Functor` has a code `∘e` for postcomposition
   with an arbitrary endofunctor, which `Grammar.Inductive.Functor` has
   no counterpart for — and rightly so, since an arbitrary endofunctor
   need not have an initial algebra. `isPoly` cuts out the fragment
   that does correspond: the purely polynomial codes.

   On that fragment the two interpretations agree up to the `LiftG`s
   that `Grammar.Inductive` needs for universe polymorphism and that a
   model, having a single level of objects, does not. That isomorphism
   is `tr`, and `isSetValued⌊⌋` supplies what
   `Grammar.Inductive.HLevels.isSetGrammarμ` needs to conclude that the
   corresponding fixed point is set-valued — which is what makes it an
   object of the families model at all.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Instances.FamiliesInductive (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Empty as Empty

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet hiding (⟨_⟩)
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Lift.Base Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.Sum.Properties Alphabet
open import Grammar.Product.Base Alphabet
open import Grammar.Product.Properties Alphabet
open import Term.Base Alphabet

import Grammar.Inductive.Functor
import Grammar.Inductive.HLevels
import Semantics.Inductive.Functor
import Semantics.Notation

open import Semantics.Instances.Families Alphabet

module Ind = Grammar.Inductive.Functor Alphabet
module IndH = Grammar.Inductive.HLevels Alphabet

open StrongEquivalence

module _ (ℓ : Level) (Gen : hSet ℓ) (lit : ⟨ Gen ⟩ → SetGrammar ℓ) where
  private
    M = FamiliesOn ℓ Gen lit

  module Sem = Semantics.Inductive.Functor M
  module N = Semantics.Notation M

  private
    variable
      X : Type ℓ

  -- | The polynomial fragment: no `∘e` nodes.
  isPoly : Sem.Functor X → Type ℓ
  isPoly (Sem.k A) = Unit*
  isPoly (Sem.Var x) = Unit*
  isPoly (Sem.&e Y F) = ∀ y → isPoly (F y)
  isPoly (Sem.⊕e Y F) = ∀ y → isPoly (F y)
  isPoly (F Sem.⊗e F') = isPoly F × isPoly F'
  isPoly (Sem.∘e E F) = Empty.⊥*

  -- | Translation into the codes of `Grammar.Inductive`.
  ⌊_⌋ : (F : Sem.Functor X) → isPoly F → Ind.Functor X
  ⌊ Sem.k A ⌋ p = Ind.k (A .fst)
  ⌊ Sem.Var x ⌋ p = Ind.Var x
  ⌊ Sem.&e Y F ⌋ p = Ind.&e ⟨ Y ⟩ λ y → ⌊ F y ⌋ (p y)
  ⌊ Sem.⊕e Y F ⌋ p = Ind.⊕e ⟨ Y ⟩ λ y → ⌊ F y ⌋ (p y)
  ⌊ F Sem.⊗e F' ⌋ p = ⌊ F ⌋ (p .fst) Ind.⊗e ⌊ F' ⌋ (p .snd)
  ⌊ Sem.∘e E F ⌋ p = Empty.rec* p

  -- | The translated code is set-valued, so its fixed point is a
  --   legitimate object of the families model.
  isSetValued⌊⌋ : (F : Sem.Functor X) (p : isPoly F)
                → IndH.isSetValued (⌊ F ⌋ p)
  isSetValued⌊⌋ (Sem.k A) p = A .snd
  isSetValued⌊⌋ (Sem.Var x) p = tt*
  isSetValued⌊⌋ (Sem.&e Y F) p = λ y → isSetValued⌊⌋ (F y) (p y)
  isSetValued⌊⌋ (Sem.⊕e Y F) p = Y .snd , λ y → isSetValued⌊⌋ (F y) (p y)
  isSetValued⌊⌋ (F Sem.⊗e F') p =
    isSetValued⌊⌋ F (p .fst) , isSetValued⌊⌋ F' (p .snd)
  isSetValued⌊⌋ (Sem.∘e E F) p = Empty.rec* p

  -- | The two interpretations agree up to LiftG.
  tr : (F : Sem.Functor X) (p : isPoly F) (A : X → SetGrammar ℓ)
     → Sem.⟦ F ⟧ A .fst ≅ Ind.⟦ ⌊ F ⌋ p ⟧ (λ x → A x .fst)
  tr (Sem.k A) p _ = LiftG≅ ℓ (A .fst)
  tr (Sem.Var x) p A = LiftG≅ ℓ (A x .fst)
  tr (Sem.&e Y F) p A = &ᴰ≅ λ y → tr (F y) (p y) A
  tr (Sem.⊕e Y F) p A = ⊕ᴰ≅ λ y → tr (F y) (p y) A
  tr (F Sem.⊗e F') p A = ⊗≅ (tr F (p .fst) A) (tr F' (p .snd) A)
  tr (Sem.∘e E F) p A = Empty.rec* p
