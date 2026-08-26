{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Thompson's construction at `satr`: two states, and one transition for
   each character satisfying the predicate.

   This is `literalNFA` with `Unit` replaced by `Sat P`, which is why the
   whole construction needs a finite alphabet: an NFA's transitions are a
   `FinSet`, and there is one per satisfying character. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.WildCat.LocallySmall.Base
open import Cubical.Data.FinSet
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Thompson.Construction.Sat
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet)
  (isFinSetAlphabet : isFinSet Alphabet)
  where

open import Cubical.Relation.Nullary.Base using (Discrete)
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.Properties using (isFinSetUnit)
open import Cubical.Data.SumFin using (Fin ; fzero ; isSetFin)
open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
  renaming (_≟_ to _≟Bool_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
import Cubical.HITs.PropositionalTruncation as PT

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⊗ε-unit-r ; ⊗ε-unit-r⁻)
open import Theory.Instances.Monoid.Unitor Alphabet isSetAlphabet
  using (⊗-unit-r∘r⁻ ; ⊗-unit-r⁻∘r)
open import Theory.Instances.Monoid.Automata.NFA.Base Alphabet isSetAlphabet

open WildCatNotation
open WildCatIso
open Iso
open NFA

-- `Regex.Sat`'s `Sat` and `satG`, restated here so that Thompson does not
-- import the decidable-parser stack that `Regex.Base` re-exports.
Sat : (Alphabet → Bool) → Type ℓAlph
Sat P = Σ[ c ∈ Alphabet ] (P c ≡ true)

satG : (P : Alphabet → Bool) → TheoryTy ℓM tt
satG P = ⊕[ x ∈ Sat P ] literal (x .fst)

isFinSetSat : (P : Alphabet → Bool) → isFinSet (Sat P)
isFinSetSat P = isFinSetΣ (Alphabet , isFinSetAlphabet) λ c →
  _ , isDecProp→isFinSet (isSetBool (P c) true) (P c ≟Bool true)

module _ (P : Alphabet → Bool) where
  data STATE : Type ℓ-zero where
    c-st ε-st : STATE

  STATE≅Fin2 : Iso STATE (Fin 2)
  STATE≅Fin2 .fun c-st = fzero
  STATE≅Fin2 .fun ε-st = Sum.inr fzero
  STATE≅Fin2 .inv fzero = c-st
  STATE≅Fin2 .inv (Sum.inr _) = ε-st
  STATE≅Fin2 .sec fzero = refl
  STATE≅Fin2 .sec (Sum.inr fzero) = refl
  STATE≅Fin2 .ret c-st = refl
  STATE≅Fin2 .ret ε-st = refl

  satNFA : NFA ℓAlph
  satNFA .Q = Lift ℓAlph STATE
    , EquivPresIsFinSet LiftEquiv (2 , PT.∣ isoToEquiv STATE≅Fin2 ∣₁)
  satNFA .init = lift c-st
  satNFA .isAcc (lift c-st) = false
  satNFA .isAcc (lift ε-st) = true
  satNFA .transition = Sat P , isFinSetSat P
  satNFA .src _ = lift c-st
  satNFA .dst _ = lift ε-st
  satNFA .label x = x .fst
  satNFA .ε-transition = Lift ℓAlph Empty.⊥
    , EquivPresIsFinSet LiftEquiv isFinSet⊥
  satNFA .ε-src ()
  satNFA .ε-dst ()

  open NFA.Accepting satNFA

  ℓsat : Level
  ℓsat = ℓF (ℓ⋆ ℓAlph)

  ⟦_⟧st : Lift ℓAlph STATE → TheoryTy ℓsat tt
  ⟦ lift c-st ⟧st = LiftTheoryTy ℓsat (satG P)
  ⟦ lift ε-st ⟧st = LiftTheoryTy ℓsat εTy

  satAlg : TraceAlg ⟦_⟧st
  satAlg (lift c-st) = ⊕ᴰ-elim λ where
    (step t Eq.refl) →
      liftTy ∘⊢ σ⊕ t ∘⊢ ⊗ε-unit-r ∘⊢ ⊗-map id⊢ lowerTy ∘⊢ step-out t Eq.refl
  satAlg (lift ε-st) = ⊕ᴰ-elim λ where
    (stop Eq.refl) → liftTy ∘⊢ lowerTy ∘⊢ lowerTy

  fromNFA : ∀ q → Trace q ⊢ ⟦ q ⟧st
  fromNFA = rec TraceTy satAlg

  toNFA : ∀ q → ⟦ q ⟧st ⊢ Trace q
  toNFA (lift c-st) =
    ⊕ᴰ-elim (λ t → STEP t ∘⊢ ⊗-map id⊢ (STOP Eq.refl) ∘⊢ ⊗ε-unit-r⁻)
      ∘⊢ lowerTy
  toNFA (lift ε-st) = STOP Eq.refl ∘⊢ lowerTy

  private
    pre : ∀ t → ⟦ branch (lift c-st) (step t Eq.refl) ⟧TheoryTy ⟦_⟧st
              ⊢ literal (t .fst) ⊗ εTy
    pre t = ⊗-map id⊢ lowerTy ∘⊢ step-out t Eq.refl

    post : ∀ t → literal (t .fst) ⊗ εTy ⊢ Trace (lift c-st)
    post t = STEP t ∘⊢ ⊗-map id⊢ (STOP Eq.refl)

    roll↑ : ∀ t → (⟦ branch (lift c-st) (step t Eq.refl) ⟧TheoryTy ⟦_⟧st
                  ⊢ ⟦ branch (lift c-st) (step t Eq.refl) ⟧TheoryTy Trace)
                → ⟦ branch (lift c-st) (step t Eq.refl) ⟧TheoryTy ⟦_⟧st
                  ⊢ Trace (lift c-st)
    roll↑ t z = roll ∘⊢ σ⊕ (step t Eq.refl) ∘⊢ z

  toNFA-homo : ∀ q → toNFA q ∘⊢ satAlg q ≡ roll ∘⊢ map (TraceTy q) toNFA
  toNFA-homo (lift c-st) = ⊕ᴰ≡ _ _ λ where
    (step t Eq.refl) →
      cong (λ z → post t ∘⊢ z ∘⊢ pre t) (⊗-unit-r⁻∘r {A = literal (t .fst)})
      ∙ cong (roll↑ t) (sym (map-step toNFA t Eq.refl))
  toNFA-homo (lift ε-st) = ⊕ᴰ≡ _ _ λ where (stop Eq.refl) → refl

  satNFA≅ : Parse ≅ LiftTheoryTy ℓsat (satG P)
  satNFA≅ .fun = fromNFA (lift c-st)
  satNFA≅ .inv = toNFA (lift c-st)
  satNFA≅ .sec = cong (λ z → liftTy ∘⊢ z ∘⊢ lowerTy)
    (⊕ᴰ≡ _ _ λ t → cong (σ⊕ t ∘⊢_) (⊗-unit-r∘r⁻ {A = literal (t .fst)}))
  satNFA≅ .ret = rec-section TraceTy satAlg toNFA toNFA-homo (lift c-st)
