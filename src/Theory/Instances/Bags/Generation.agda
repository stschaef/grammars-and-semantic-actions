{- Every bag can be arranged: `(m : Bag) → ∥ Seq m ∥₁`.

   Truncated, because the arrangement is not determined -- `comm` identifies
   the two orders of `a ⊙ b`, so a bag has many sequences and no canonical
   one.  With the truncation the total space `Σ[ m ∈ Bag ] ∥ Seq m ∥₁` is
   itself a model of the bag theory, whose operations are `[]ᵍ` and `_++ᵍ_`
   and whose equations hold because the second component is a prop.  So the
   bridge is again just a fold, and its uniqueness is what identifies the
   bag it lands over with the one it started from.

   This is what makes `quicksort` a statement about *bags*: without it the
   sorter takes an arrangement and says nothing about the bags that have
   none in hand. -}
{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
import Cubical.Algebra.Theory.Finitary.Free.Closing as Cl
import Cubical.Data.Equality as Eq
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open SortedSig
open SortedEqns
module Theory.Instances.Bags.Generation
  (El : Type ℓ-zero) (isSetEl : isSet El) where

open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.PropositionalTruncation as PT
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Bags.Base El
open import Theory.Instances.Bags.Sequence El
open import Theory.Instances.Bags.Sequence.Fold El isSetEl using (_++ᵍ_)

private
  Arranged : Sorts → Type (ℓF ℓM)
  Arranged _ = Σ[ m ∈ Bag ] ∥ Seq m ∥₁

  isSetArranged : ∀ s → isSet (Arranged s)
  isSetArranged _ = isSetΣ (M .fst tt .snd) λ _ → isProp→isSet squash₁

  -- The model structure: the empty arrangement and concatenation, which is
  -- exactly what `Sequence` provides.
  ArrangedOps : Ops {σ = MonSig} Arranged
  ArrangedOps ε· f = εᵖ , ∣ []ᵍ ∣₁
  ArrangedOps _⊙_ f =
    f zero .fst ⊙ᵖ f (suc zero) .fst
    , PT.rec2 squash₁ (λ s t → ∣ s ++ᵍ t ∣₁) (f zero .snd) (f (suc zero) .snd)

  -- Every equation is one in `Bag` alone: the arrangement component is a
  -- prop, so `Σ≡Prop` discharges it and no sequence has to be moved.
  ArrangedSat : (e : BagEqns .eqns)
         (ρ : (w : vars BagEqns e) → Arranged (BagEqns .varSort e w))
       → TmRec Arranged ArrangedOps ρ (BagEqns .lhs e)
       ≡ TmRec Arranged ArrangedOps ρ (BagEqns .rhs e)
  ArrangedSat e ρ = Σ≡Prop (λ _ → squash₁) (bagPath e ρ)
    where
    bagPath : (e : BagEqns .eqns)
              (ρ : (w : vars BagEqns e) → Arranged (BagEqns .varSort e w))
            → TmRec Arranged ArrangedOps ρ (BagEqns .lhs e) .fst
            ≡ TmRec Arranged ArrangedOps ρ (BagEqns .rhs e) .fst
    bagPath (mon assoc) ρ =
      ⊙-assoc (ρ zero .fst) (ρ (suc zero) .fst) (ρ (suc (suc zero)) .fst)
    bagPath (mon unitL) ρ = ⊙-unitL (ρ zero .fst)
    bagPath (mon unitR) ρ = ⊙-unitR (ρ zero .fst)
    bagPath (ext comm) ρ = ⊙-comm (ρ zero .fst) (ρ (suc zero) .fst)

  fold : Bag → Arranged tt
  fold = Cl.rec BagEqns isSetArranged ArrangedOps ArrangedSat
           λ y → ⌈gen y ⌉ , ∣ singleᵍ y ∣₁

  -- The fold lands over the bag it started from.  Both sides are folds into
  -- `Bag` agreeing on generators, so this is uniqueness of homomorphisms
  -- rather than an induction over bags.
  fold-fst : (m : Bag) → fold m .fst ≡ m
  fold-fst m =
    (Cl.recUniq BagEqns (λ s → M .fst s .snd) op (M .snd .snd)
          (λ y → ⌈gen y ⌉) (λ _ z → fold z .fst)
          (λ where
            ε· u y eq → cong (λ z → fold z .fst) eq
                        ∙ cong (op ε·) (funExt λ ())
            _⊙_ u y eq → cong (λ z → fold z .fst) eq
                        ∙ cong (op _⊙_) (funExt λ where
                            zero → refl
                            (suc zero) → refl))
          (λ _ → refl) m)
    ∙ sym (Cl.recUniq BagEqns (λ s → M .fst s .snd) op (M .snd .snd)
             (λ y → ⌈gen y ⌉) (λ _ m → m) (λ o x y eq → eq) (λ _ → refl) m)

arrange : (m : Bag) → ∥ Seq m ∥₁
arrange m = subst (λ z → ∥ Seq z ∥₁) (fold-fst m) (fold m .snd)
