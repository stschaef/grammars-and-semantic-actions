{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The alphabet of the list-literal example: three punctuation tokens and a
   number.

   Split out of `Combinator/{Decidable,Incomplete}/ListLit`, which each
   carried their own copy of this datatype and of the sixteen-clause
   decision table, so that `Combinator/Grammars/ListLit` can name it once
   and be parametric in the answer -- the same arrangement `Grammars/Dyck`
   already has. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Grammars.ListLit where

-- three tokens: `[`, `]`, `,`, and a number `n`
data Tok : Type ℓ-zero where
  lb rb cm nm : Tok

_≟T_ : (x y : Tok) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
lb ≟T lb = Sum.inl Eq.refl
rb ≟T rb = Sum.inl Eq.refl
cm ≟T cm = Sum.inl Eq.refl
nm ≟T nm = Sum.inl Eq.refl
lb ≟T rb = Sum.inr λ ()
lb ≟T cm = Sum.inr λ ()
lb ≟T nm = Sum.inr λ ()
rb ≟T lb = Sum.inr λ ()
rb ≟T cm = Sum.inr λ ()
rb ≟T nm = Sum.inr λ ()
cm ≟T lb = Sum.inr λ ()
cm ≟T rb = Sum.inr λ ()
cm ≟T nm = Sum.inr λ ()
nm ≟T lb = Sum.inr λ ()
nm ≟T rb = Sum.inr λ ()
nm ≟T cm = Sum.inr λ ()
