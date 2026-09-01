{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `readChars` is the unique `char *` witness.  `Strings.read-section` does
   not apply: `String*` and `char *` are the same code under branch functions
   that never compare, and `Strings` cannot define `char *` (`KleeneStar`
   imports it).  Instead `char *` is a proposition, by seq. unambiguity. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.KleeneStar.Read
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Unit using (tt)
import Cubical.Data.Sum as Sum

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⊗ε-unit-r⁻)
open import Theory.Instances.Monoid.Precise Alphabet isSetAlphabet
  using (char⊗-precise)
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet
  using (_* ; readChars)
open import Theory.Instances.Monoid.KleeneStar.Unambiguous
  Alphabet isSetAlphabet
  using (SeqUnambig ; unambiguous-* ; _∉FollowLast_ ; startsWith)
open import Theory.Instances.Monoid.SequentialUnambiguity.First
  Alphabet isSetAlphabet
  using (startsWith→char⁺ ; char⁺-¬Nullable ; ¬Nullable→¬ε ; char-¬Nullable)

-- A `char` continued by a character would be two letters long:
-- `char⊗-precise` pins the splitting, so refuting the tail refutes the tensor.
char∉FollowLast : (c : Alphabet) → c ∉FollowLast char
char∉FollowLast c =
  ⇒-app
  ∘⊢ ((char⊗-precise
       ∘⊢ ⊗-map id⊢ (¬Nullable→¬ε char⁺-¬Nullable)
       ∘⊢ ⊗ε-unit-r⁻ ∘⊢ π₂)
      ,& (⊗-map id⊢ (startsWith→char⁺ c) ∘⊢ π₁))

char-SeqUnambig : SeqUnambig char
char-SeqUnambig c = Sum.inl (char∉FollowLast c)

unambiguous-char* : (m : String) → isProp ((char *) m)
unambiguous-char* =
  unambiguous-* char-¬Nullable char-SeqUnambig unambiguous-char

readChars-section : readChars ∘⊢ ⊤Ty-intro ≡ id⊢
readChars-section =
  funExt λ m → funExt λ xs → unambiguous-char* m (readChars m tt) xs
