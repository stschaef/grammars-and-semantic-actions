{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The same parser at several widths.  `Gram k` is

     S ::= aᵏ⁺¹ S b | aᵏ⁺¹ c

   which no width below k+2 separates; the module is instantiated at three
   of them and nothing but the index changes. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Combinator.Decidable.WidthsTests where

open import Cubical.Data.List using ([] ; _∷_)
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Combinator.Decidable.Widths
open import Theory.Instances.Monoid.Combinator.Decidable.Window Tok _≟T_ (ℓ-suc ℓ-zero)

------------------------------------------------------------------------
-- k = 0: `S ::= a S b | a c`, separated at width 2, not at width 1.

module K0 = Gram none
L0 = K0.Lang St

k0-flat : L0 (ta ∷ tc ∷ [])
k0-flat = theYes (K0.parse (ta ∷ tc ∷ []) tt) Eq.refl

k0-nest : L0 (ta ∷ ta ∷ tc ∷ tb ∷ [])
k0-nest = theYes (K0.parse (ta ∷ ta ∷ tc ∷ tb ∷ []) tt) Eq.refl

k0-nest2 : L0 (ta ∷ ta ∷ ta ∷ tc ∷ tb ∷ tb ∷ [])
k0-nest2 = theYes (K0.parse (ta ∷ ta ∷ ta ∷ tc ∷ tb ∷ tb ∷ []) tt) Eq.refl

k0-no-nil : ¬Ty L0 []
k0-no-nil = theNo (K0.parse [] tt) Eq.refl

k0-no-ab : ¬Ty L0 (ta ∷ tb ∷ [])
k0-no-ab = theNo (K0.parse (ta ∷ tb ∷ []) tt) Eq.refl

k0-no-unbalanced : ¬Ty L0 (ta ∷ ta ∷ tc ∷ [])
k0-no-unbalanced = theNo (K0.parse (ta ∷ ta ∷ tc ∷ []) tt) Eq.refl

k0-no-extra-b : ¬Ty L0 (ta ∷ tc ∷ tb ∷ [])
k0-no-extra-b = theNo (K0.parse (ta ∷ tc ∷ tb ∷ []) tt) Eq.refl

------------------------------------------------------------------------
-- k = 1: two leading `a`s, so width 3 is needed.

module K1 = Gram (more none)
L1 = K1.Lang St

k1-flat : L1 (ta ∷ ta ∷ tc ∷ [])
k1-flat = theYes (K1.parse (ta ∷ ta ∷ tc ∷ []) tt) Eq.refl

k1-nest : L1 (ta ∷ ta ∷ ta ∷ ta ∷ tc ∷ tb ∷ [])
k1-nest = theYes (K1.parse (ta ∷ ta ∷ ta ∷ ta ∷ tc ∷ tb ∷ []) tt) Eq.refl

k1-no-short : ¬Ty L1 (ta ∷ tc ∷ [])
k1-no-short = theNo (K1.parse (ta ∷ tc ∷ []) tt) Eq.refl

k1-no-b : ¬Ty L1 (ta ∷ ta ∷ tb ∷ [])
k1-no-b = theNo (K1.parse (ta ∷ ta ∷ tb ∷ []) tt) Eq.refl

------------------------------------------------------------------------
-- k = 2: three leading `a`s, width 4.

module K2 = Gram (more (more none))
L2 = K2.Lang St

k2-flat : L2 (ta ∷ ta ∷ ta ∷ tc ∷ [])
k2-flat = theYes (K2.parse (ta ∷ ta ∷ ta ∷ tc ∷ []) tt) Eq.refl

k2-nest : L2 (ta ∷ ta ∷ ta ∷ ta ∷ ta ∷ ta ∷ tc ∷ tb ∷ [])
k2-nest = theYes (K2.parse (ta ∷ ta ∷ ta ∷ ta ∷ ta ∷ ta ∷ tc ∷ tb ∷ []) tt) Eq.refl

k2-no-short : ¬Ty L2 (ta ∷ ta ∷ tc ∷ [])
k2-no-short = theNo (K2.parse (ta ∷ ta ∷ tc ∷ []) tt) Eq.refl
