{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `regex→NFA` over the nullability-indexed `RE`.  `satr` needs one transition
   per satisfying character (finite alphabet); `reLevel` records each regex's non-constant state level. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.FinSet
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Thompson.Base
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet)
  (isFinSetAlphabet : isFinSet Alphabet)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Relation.Nullary.DecidablePropositions.More
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.Properties using (isFinSetBool)
open import Cubical.Data.Bool using (Bool ; true)
  renaming (_≟_ to _≟Bool_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Regex.Base Alphabet _≟_ ℓ
  using (RE ; εr ; ⊥r ; ⟨_⟩r ; satr ; _⊗r_ ; _⊕r_ ; _*r)
open import Theory.Instances.Monoid.Automata.NFA.Base Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Thompson.Construction
  Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Thompson.Construction.Sat
  Alphabet isSetAlphabet isFinSetAlphabet
  using (satNFA ; satNFA≅ ; Sat ; satG)
  renaming (STATE≅Fin2 to satSTATE≅Fin2)

open NFA

reLevel : ∀ {n} → RE n → Level
reLevel εr = ℓ-zero
reLevel ⊥r = ℓ-zero
reLevel ⟨ _ ⟩r = ℓ-zero
reLevel (satr _) = ℓAlph
reLevel (r ⊗r r') = ℓ-max (reLevel r) (reLevel r')
reLevel (r ⊕r r') = ℓ-max (reLevel r) (reLevel r')
reLevel (r *r) = reLevel r

regex→NFA : ∀ {n} (r : RE n) → NFA (reLevel r)
regex→NFA εr = εNFA
regex→NFA ⊥r = ⊥NFA
regex→NFA ⟨ c ⟩r = literalNFA c
regex→NFA (satr P) = satNFA P
regex→NFA (r ⊗r r') = ⊗NFA (regex→NFA r) (regex→NFA r')
regex→NFA (r ⊕r r') = ⊕NFA (regex→NFA r) (regex→NFA r')
regex→NFA (r *r) = *NFA (regex→NFA r)

-- finitely *ordered*, not merely finite: what a determinisation enumerates over
module _ (isFinOrdAlphabet : isFinOrd Alphabet) where
  private
    isFinOrdSat : (P : Alphabet → Bool) → isFinOrd (Sat P)
    isFinOrdSat P = isFinOrdΣ Alphabet isFinOrdAlphabet _ λ c →
      DecProp→isFinOrd (DecProp≡ _≟Bool_ (P c) true)

  isFinOrdStates : ∀ {n} (r : RE n) → isFinOrd ⟨ regex→NFA r .Q ⟩
  isFinOrdStates εr = isFinOrdUnit
  isFinOrdStates ⊥r = isFinOrdUnit
  isFinOrdStates ⟨ c ⟩r =
    EquivPresIsFinOrd (invEquiv (isoToEquiv (STATE≅Fin2 c)))
      (isFinOrd⊎ _ isFinOrdUnit _ (isFinOrd⊎ _ isFinOrdUnit _ isFinOrd⊥))
  isFinOrdStates (satr P) =
    EquivPresIsFinOrd (invEquiv (isoToEquiv (satSTATE≅Fin2 P)) ∙ₑ LiftEquiv)
      (isFinOrd⊎ _ isFinOrdUnit _ (isFinOrd⊎ _ isFinOrdUnit _ isFinOrd⊥))
  isFinOrdStates (r ⊗r r') =
    isFinOrd⊎ _ (isFinOrdStates r) _ (isFinOrdStates r')
  isFinOrdStates (r ⊕r r') =
    EquivPresIsFinOrd (invEquiv (⊕State-rep (regex→NFA r) (regex→NFA r')))
      (isFinOrd⊎ _ isFinOrdUnit _
        (isFinOrd⊎ _ (isFinOrdStates r) _ (isFinOrdStates r')))
  isFinOrdStates (r *r) = isFinOrd⊎ _ isFinOrdUnit _ (isFinOrdStates r)

  isFinOrdTransition :
    ∀ {n} (r : RE n) → isFinOrd ⟨ regex→NFA r .transition ⟩
  isFinOrdTransition εr = isFinOrd⊥
  isFinOrdTransition ⊥r = isFinOrd⊥
  isFinOrdTransition ⟨ c ⟩r = isFinOrdUnit
  isFinOrdTransition (satr P) = isFinOrdSat P
  isFinOrdTransition (r ⊗r r') =
    isFinOrd⊎ _ (isFinOrdTransition r) _ (isFinOrdTransition r')
  isFinOrdTransition (r ⊕r r') =
    isFinOrd⊎ _ (isFinOrdTransition r) _ (isFinOrdTransition r')
  isFinOrdTransition (r *r) = isFinOrdTransition r

  isFinOrdεTransition :
    ∀ {n} (r : RE n) → isFinOrd ⟨ regex→NFA r .ε-transition ⟩
  isFinOrdεTransition εr = isFinOrd⊥
  isFinOrdεTransition ⊥r = isFinOrd⊥
  isFinOrdεTransition ⟨ c ⟩r = isFinOrd⊥
  isFinOrdεTransition (satr P) = EquivPresIsFinOrd LiftEquiv isFinOrd⊥
  isFinOrdεTransition (r ⊗r r') =
    EquivPresIsFinOrd (⊗εTrans-rep (regex→NFA r) (regex→NFA r'))
      (isFinOrd⊎ _
        (isFinOrdΣ ⟨ regex→NFA r .Q ⟩ (isFinOrdStates r) _
          λ q → DecProp→isFinOrd
            (isFinSet→DecProp-Eq≡ isFinSetBool true (regex→NFA r .isAcc q)))
        _ (isFinOrd⊎ _ (isFinOrdεTransition r) _ (isFinOrdεTransition r')))
  isFinOrdεTransition (r ⊕r r') =
    EquivPresIsFinOrd (⊕εTrans-rep (regex→NFA r) (regex→NFA r'))
      (isFinOrd⊎ _ isFinOrdUnit _
        (isFinOrd⊎ _ isFinOrdUnit _
          (isFinOrd⊎ _ (isFinOrdεTransition r) _ (isFinOrdεTransition r'))))
  isFinOrdεTransition (r *r) =
    EquivPresIsFinOrd (*εTrans-rep (regex→NFA r))
      (isFinOrd⊎ _ isFinOrdUnit _
        (isFinOrd⊎ _
          (isFinOrdΣ _ (isFinOrdStates r) _
            λ q → DecProp→isFinOrd
              (isFinSet→DecProp-Eq≡ isFinSetBool true (regex→NFA r .isAcc q)))
          _ (isFinOrdεTransition r)))
