{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- Decidable equality stated in `Eq.≡` rather than in `Path`.

   The parsers index on their alphabet, and matching on an `Eq.≡` proof
   refines that index where matching on a `Path` cannot.  Nothing here
   mentions a theory: this is the metalanguage side of `Decidable`. -}
open import Cubical.Foundations.Prelude
module Theory.Type.Decidable.DiscreteEq where

open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Unit using (Unit)
import Cubical.Data.Sum as Sum
import Cubical.Data.Equality as Eq

private variable ℓY ℓZ : Level

DiscreteEq : ∀ {ℓY} → Type ℓY → Type ℓY
DiscreteEq Y = (y y' : Y) → (y Eq.≡ y') Sum.⊎ ((y Eq.≡ y') → ⊥)

-- Carried back along a retraction.  An enumeration -- a datatype all of
-- whose constructors are nullary -- is a retract of `ℕ` by the
-- constructor's index, so its `DiscreteEq` costs one clause per
-- constructor rather than one per ordered pair of them.
decEqRetract : {Y : Type ℓY} {Z : Type ℓZ}
  (code : Y → Z) (decode : Z → Y)
  → ((y : Y) → decode (code y) Eq.≡ y)
  → DiscreteEq Z → DiscreteEq Y
decEqRetract code decode decode∘code decZ y y' with decZ (code y) (code y')
... | Sum.inl codesAgree =
  Sum.inl (Eq.sym (decode∘code y)
           Eq.∙ Eq.ap decode codesAgree
           Eq.∙ decode∘code y')
... | Sum.inr codesDiffer = Sum.inr λ y≡y' → codesDiffer (Eq.ap code y≡y')

decℕEq : DiscreteEq ℕ
decℕEq zero zero = Sum.inl Eq.refl
decℕEq zero (suc _) = Sum.inr λ ()
decℕEq (suc _) zero = Sum.inr λ ()
decℕEq (suc m) (suc n) with decℕEq m n
... | Sum.inl Eq.refl = Sum.inl Eq.refl
... | Sum.inr m≢n = Sum.inr λ where Eq.refl → m≢n Eq.refl

-- Enumerations, which is what the retraction above is for.  `index` is
-- one clause per constructor and `table` lists them in that order; a code
-- out of range cannot arise from `index`, so `table` needs no totality
-- proof and `nth` answers off the end with the first constructor.
nth : {Y : Type ℓY} → Y → List Y → ℕ → Y
nth fallback [] _ = fallback
nth fallback (y ∷ _) zero = y
nth fallback (_ ∷ ys) (suc n) = nth fallback ys n

decEqEnum : {Y : Type ℓY} (fallback : Y) (index : Y → ℕ) (table : List Y)
  → ((y : Y) → nth fallback table (index y) Eq.≡ y)
  → DiscreteEq Y
decEqEnum fallback index table indexed =
  decEqRetract index (nth fallback table) indexed decℕEq

decUnitEq : DiscreteEq Unit
decUnitEq _ _ = Sum.inl Eq.refl

dec⊎Eq : {Y : Type ℓY} {Z : Type ℓZ}
  → DiscreteEq Y → DiscreteEq Z → DiscreteEq (Y Sum.⊎ Z)
dec⊎Eq decY decZ (Sum.inl y) (Sum.inl y') with decY y y'
... | Sum.inl Eq.refl = Sum.inl Eq.refl
... | Sum.inr y≢y' = Sum.inr λ where Eq.refl → y≢y' Eq.refl
dec⊎Eq decY decZ (Sum.inr z) (Sum.inr z') with decZ z z'
... | Sum.inl Eq.refl = Sum.inl Eq.refl
... | Sum.inr z≢z' = Sum.inr λ where Eq.refl → z≢z' Eq.refl
dec⊎Eq decY decZ (Sum.inl _) (Sum.inr _) = Sum.inr λ ()
dec⊎Eq decY decZ (Sum.inr _) (Sum.inl _) = Sum.inr λ ()
