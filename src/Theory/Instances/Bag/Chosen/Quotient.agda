{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `¬descendsSorted`: NO predicate on bags induces `Sorted`, so that client
   decides a property of LISTS.  `descendsOccurs`: membership descends, being
   a fold out of the free algebra.  Its truncation is `⊔`'s artefact, not the
   quotient's; WHICH occurrence is unrecoverable (cf. `¬preciseNode`). -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Algebra.Theory.Finitary
import Cubical.Algebra.Theory.Finitary.Free.Closing as Cl
import Cubical.Data.Equality as Eq
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open SortedSig
open SortedEqns
module Theory.Instances.Bag.Chosen.Quotient
  (El : Type ℓ-zero) (isSetEl : isSet El) (le : El → El → Bool) where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Maybe using (Maybe ; nothing ; just)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.HITs.PropositionalTruncation as PT
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Relation.Nullary.Base using (¬_)
import Cubical.Data.Sum as Sum
import Cubical.Functions.Logic as L

open import Theory.Instances.Monoid.Base using (Sorts ; MonSig ; MonOp
  ; ε· ; _⊙_ ; MonEqn ; assoc ; unitL ; unitR)
open import Theory.Instances.Bags.Base El
  using (Bag ; BagEqns ; CommEqn ; comm ; mon ; ext
        ; _⊙ᵖ_ ; εᵖ ; ⌈gen_⌉ ; ⊙-comm ; ⊙-assoc ; ⊙-unitR)

import Theory.Instances.Bag.Chosen.Sorted El isSetEl le as S
import Theory.Instances.Bag.Chosen.Occurs El isSetEl as O

private variable ℓ : Level

toBag : List El → Bag
toBag [] = εᵖ
toBag (x ∷ l) = ⌈gen x ⌉ ⊙ᵖ toBag l

-- One transposition generates every permutation, so this is the whole of
-- what a predicate on representatives must be blind to.
toBag-swap : (x y : El) (l : List El)
  → toBag (x ∷ y ∷ l) ≡ toBag (y ∷ x ∷ l)
toBag-swap x y l =
    sym (⊙-assoc ⌈gen x ⌉ ⌈gen y ⌉ (toBag l))
  ∙ cong (_⊙ᵖ toBag l) (⊙-comm ⌈gen x ⌉ ⌈gen y ⌉)
  ∙ ⊙-assoc ⌈gen y ⌉ ⌈gen x ⌉ (toBag l)

Descends : (List El → Type ℓ) → Type (ℓ-suc ℓ)
Descends {ℓ = ℓ} A =
  Σ[ P ∈ (Bag → Type ℓ) ]
    (((l : List El) → A l → P (toBag l))
     × ((l : List El) → P (toBag l) → A l))


module _ (x y : El) (below : le x y Eq.≡ true) (above : le y x Eq.≡ false)
  where

  private
    lo : List El
    lo = x ∷ y ∷ []

    hi : List El
    hi = y ∷ x ∷ []

    sortedLo : S.Sorted nothing lo
    sortedLo = tt , (below , tt)

    ¬sortedHi : ¬ S.Sorted nothing hi
    ¬sortedHi (_ , (q , _)) =
      true≢false (sym (Eq.eqToPath q) ∙ Eq.eqToPath above)

  ¬descendsSorted : ¬ Descends (S.Sorted nothing)
  ¬descendsSorted (P , (into , out)) =
    ¬sortedHi (out hi (subst P (toBag-swap x y []) (into lo sortedLo)))


private
  Ω : Sorts → Type (ℓ-suc ℓ-zero)
  Ω _ = hProp ℓ-zero

  ⊔Ops : Ops {σ = MonSig} Ω
  ⊔Ops ε· f = L.⊥
  ⊔Ops _⊙_ f = L._⊔_ (f zero) (f (suc zero))

  ⊔Sat : (e : BagEqns .eqns)
         (ρ : (w : vars BagEqns e) → Ω (BagEqns .varSort e w))
       → TmRec Ω ⊔Ops ρ (BagEqns .lhs e) ≡ TmRec Ω ⊔Ops ρ (BagEqns .rhs e)
  ⊔Sat (mon assoc) ρ =
    sym (L.⊔-assoc (ρ zero) (ρ (suc zero)) (ρ (suc (suc zero))))
  ⊔Sat (mon unitL) ρ = L.⊔-identityˡ (ρ zero)
  ⊔Sat (mon unitR) ρ = L.⊔-identityʳ (ρ zero)
  ⊔Sat (ext comm) ρ = L.⊔-comm (ρ zero) (ρ (suc zero))

  memP : El → El → hProp ℓ-zero
  memP z w = (w ≡ z) , isSetEl w z

bagAny : (El → hProp ℓ-zero) → Bag → hProp ℓ-zero
bagAny p m = Cl.rec BagEqns (λ _ → isSetHProp) ⊔Ops ⊔Sat p m

Mem : El → Bag → hProp ℓ-zero
Mem z = bagAny (memP z)

private
  into : (z : El) (l : List El) → O.Occurs z l → ⟨ Mem z (toBag l) ⟩
  into z (x ∷ l) (Sum.inl p) = L.inl p
  into z (x ∷ l) (Sum.inr o) = L.inr (into z l o)

  out : (z : El) (l : List El) → ⟨ Mem z (toBag l) ⟩ → ∥ O.Occurs z l ∥₁
  out z (x ∷ l) h =
    L.⊔-elim (memP z x) (Mem z (toBag l))
      (λ _ → ∥ O.Occurs z (x ∷ l) ∥₁ , squash₁)
      (λ p → ∣ Sum.inl p ∣₁)
      (λ q → PT.map Sum.inr (out z l q))
      h

descendsOccurs : (z : El) → Descends (λ l → ∥ O.Occurs z l ∥₁)
descendsOccurs z =
    (λ m → ⟨ Mem z m ⟩)
  , ( (λ l → PT.rec (Mem z (toBag l) .snd) (into z l))
    , out z )
