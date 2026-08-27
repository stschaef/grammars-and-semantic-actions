{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The characters a `Bool`-predicate accepts, and the grammar of one such
   character.  Split out of `Regex/Sat` so that Thompson can use it without
   the decidable-parser stack that file sits on. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Sat
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Bool using (Bool ; true ; isSetBool)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Type.HLevels MonEqns Alphabet (λ _ → tt) listPresentation
  using (TheorySet ; isSet⊕ᴰ)

Sat : (Alphabet → Bool) → Type ℓAlph
Sat P = Σ[ c ∈ Alphabet ] (P c ≡ true)

isSetSat : (P : Alphabet → Bool) → isSet (Sat P)
isSetSat P = isSetΣ isSetAlphabet λ _ → isProp→isSet (isSetBool _ _)

satG : (P : Alphabet → Bool) → TheoryTy ℓM tt
satG P = ⊕[ x ∈ Sat P ] literal (x .fst)

satSet : (P : Alphabet → Bool) → TheorySet ℓM tt
satSet P =
  satG P , isSet⊕ᴰ (isSetSat P) λ _ _ → isProp→isSet isPropEqString
