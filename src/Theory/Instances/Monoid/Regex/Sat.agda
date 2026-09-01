{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A character satisfying a decidable predicate: `satG P` is `char` restricted along `P`.
   Finite disjunction does not suffice — over `Bits 21` a complement class is two million
   disjuncts, and over an infinite alphabet it is no finite disjunction at all. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Regex.Sat
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool ; true≢false)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.List using ([] ; _∷_)
import Cubical.Data.List.Properties as L
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
open import Cubical.Foundations.HLevels using (isSetΣ)
open import Cubical.Relation.Nullary.DiscreteEq using (DiscreteEq→isSet)

isSetAlphabet : isSet Alphabet
isSetAlphabet = DiscreteEq→isSet _≟_


open import Theory.Instances.Monoid.Sat Alphabet isSetAlphabet public

