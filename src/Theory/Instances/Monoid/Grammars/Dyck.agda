{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Grammars.Dyck where

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)

-- the alphabet: one bracket pair
data Br : Type ℓ-zero where
  lp rp : Br

_≟_ : (x y : Br) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
_≟_ lp lp = Sum.inl Eq.refl
_≟_ rp rp = Sum.inl Eq.refl
_≟_ lp rp = Sum.inr λ ()
_≟_ rp lp = Sum.inr λ ()

data Dyck : Type ℓ-zero where
  done : Dyck
  nest : Dyck → Dyck → Dyck

open import Theory.Instances.Monoid.Types Br _≟_
import Theory.Instances.Monoid.Examples Br isSetAlphabet as E

dyckBranch : Bool → Functor ℓM Unit (λ _ → tt) tt
dyckBranch = E.dyckBranch lp rp

dyckF : Unit → Functor ℓM Unit (λ _ → tt) tt
dyckF _ = E.DyckCode lp rp

isSetDyckF : (x : Unit) → isSetValued (dyckF x)
isSetDyckF _ .fst = lift isSetBool
isSetDyckF _ .snd false = lift isSetεTy
isSetDyckF _ .snd true zero = lift (isSetLiteral lp)
isSetDyckF _ .snd true (suc zero) zero = lift tt*
isSetDyckF _ .snd true (suc zero) (suc zero) zero = lift (isSetLiteral rp)
isSetDyckF _ .snd true (suc zero) (suc zero) (suc zero) = lift tt*
