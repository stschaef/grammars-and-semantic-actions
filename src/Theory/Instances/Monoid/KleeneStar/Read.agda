{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `readChars` is the unique `char *` witness of a word.

   `Strings` proves this for `String*` (`read-section`), but `String*` is
   `μ X. εTy ⊕ (char ⊗ X)` under `kleeneBranch` while `char *` is the same
   code under `starBranch char`.  The two branch functions have identical
   right-hand sides, but as functions `Bool → Functor` they never compare,
   so `String*` and `char *` are different types and `read-section` does
   not apply.  `Strings` cannot define `char *` either -- `KleeneStar`
   imports it, not the other way round.

   Rather than mirror `readSq'` at the other code, get it from
   unambiguity: `char` is non-nullable, unambiguous, and sequentially
   unambiguous with itself, so `unambiguous-*` says `char *` is a
   proposition at every word -- and then *any* two terms into it agree,
   `readChars ∘⊢ ⊤Ty-intro` and `id⊢` among them. -}
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

-- No character can continue a `char`: the result would be two letters
-- long.  `char⊗-precise` is what says so internally -- the splitting of a
-- `char ⊗ _` is pinned by the word, so refuting the tail refutes the
-- tensor, and the tail of a one-letter word is empty.
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

-- ...so `readChars` is *the* list of characters of a word.
readChars-section : readChars ∘⊢ ⊤Ty-intro ≡ id⊢
readChars-section =
  funExt λ m → funExt λ xs → unambiguous-char* m (readChars m tt) xs
