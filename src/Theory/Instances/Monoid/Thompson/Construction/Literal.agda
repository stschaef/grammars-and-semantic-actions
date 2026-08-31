{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Thompson's construction at a single character: two states and one
   transition between them, the second accepting. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.WildCat.LocallySmall.Base
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Thompson.Construction.Literal
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Relation.Nullary.Base using (Discrete)
open import Cubical.Relation.Nullary.Properties using (isoPresDiscrete)
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.Properties using (isFinSetUnit)
open import Cubical.Data.SumFin using (Fin ; fzero ; isSetFin ; discreteFin)
open import Cubical.Data.Bool using (true ; false)
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

module _ (c : Alphabet) where
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

  isSetSTATE : isSet STATE
  isSetSTATE =
    isSetRetract (STATE≅Fin2 .fun) (STATE≅Fin2 .inv) (STATE≅Fin2 .ret) isSetFin

  isDiscSTATE : Discrete STATE
  isDiscSTATE = isoPresDiscrete (invIso STATE≅Fin2) discreteFin

  literalNFA : NFA ℓ-zero
  literalNFA .Q = STATE , 2 , PT.∣ isoToEquiv STATE≅Fin2 ∣₁
  literalNFA .init = c-st
  literalNFA .isAcc c-st = false
  literalNFA .isAcc ε-st = true
  literalNFA .transition = Unit , isFinSetUnit
  literalNFA .src _ = c-st
  literalNFA .dst _ = ε-st
  literalNFA .label _ = c
  literalNFA .ε-transition = Empty.⊥ , isFinSet⊥
  literalNFA .ε-src ()
  literalNFA .ε-dst ()

  open NFA.Accepting literalNFA

  ℓlit : Level
  ℓlit = ℓF (ℓ⋆ ℓ-zero)

  -- The state's language: the character is still owed at `c-st`, nothing at
  -- `ε-st`.  Both are lifted to the trace's level.
  ⟦_⟧st : STATE → TheoryTy ℓlit tt
  ⟦ c-st ⟧st = LiftTheoryTy ℓlit (literal c)
  ⟦ ε-st ⟧st = LiftTheoryTy ℓlit εTy

  litAlg : TraceAlg ⟦_⟧st
  litAlg c-st = ⊕ᴰ-elim λ where
    (step t Eq.refl) →
      liftTy ∘⊢ ⊗ε-unit-r ∘⊢ ⊗-map id⊢ lowerTy ∘⊢ step-out t Eq.refl
  litAlg ε-st = ⊕ᴰ-elim λ where (stop Eq.refl) → liftTy ∘⊢ lowerTy ∘⊢ lowerTy

  fromNFA : ∀ q → Trace q ⊢ ⟦ q ⟧st
  fromNFA = rec TraceTy litAlg

  toNFA : ∀ q → ⟦ q ⟧st ⊢ Trace q
  toNFA c-st =
    STEP tt ∘⊢ ⊗-map id⊢ (STOP Eq.refl)
      ∘⊢ ⊗ε-unit-r⁻ ∘⊢ lowerTy
  toNFA ε-st = STOP Eq.refl ∘⊢ lowerTy

  -- `toNFA` is an algebra map.  At `c-st` the composite is
  --   STEP ∘ (id ⊗ STOP) ∘ ⊗ε-unit-r⁻ ∘ ⊗ε-unit-r ∘ (id ⊗ lower) ∘ step-out,
  -- so the two unitors cancel and what is left is `map` at the `step`
  -- summand.  At `ε-st` there is nothing to do.
  private
    pre : ∀ t → ⟦ branch c-st (step t Eq.refl) ⟧TheoryTy ⟦_⟧st
              ⊢ literal c ⊗ εTy
    pre t = ⊗-map id⊢ lowerTy ∘⊢ step-out t Eq.refl

    post : ∀ t → literal c ⊗ εTy ⊢ Trace c-st
    post t = STEP t ∘⊢ ⊗-map id⊢ (STOP Eq.refl)

    -- rolling up a `step` summand, named so `cong` has a domain to solve
    roll↑ : ∀ t → (⟦ branch c-st (step t Eq.refl) ⟧TheoryTy ⟦_⟧st
                 ⊢ ⟦ branch c-st (step t Eq.refl) ⟧TheoryTy Trace)
                → ⟦ branch c-st (step t Eq.refl) ⟧TheoryTy ⟦_⟧st ⊢ Trace c-st
    roll↑ t z = roll ∘⊢ σ⊕ (step t Eq.refl) ∘⊢ z

  toNFA-homo : ∀ q → toNFA q ∘⊢ litAlg q
                   ≡ roll ∘⊢ map (TraceTy q) toNFA
  toNFA-homo c-st = ⊕ᴰ≡ _ _ λ where
    (step t Eq.refl) →
      cong (λ z → post t ∘⊢ z ∘⊢ pre t) (⊗-unit-r⁻∘r {A = literal c})
      ∙ cong (roll↑ t) (sym (map-step toNFA t Eq.refl))
  toNFA-homo ε-st = ⊕ᴰ≡ _ _ λ where (stop Eq.refl) → refl

  litNFA≅ : Trace c-st ≅ LiftTheoryTy ℓlit (literal c)
  litNFA≅ .fun = fromNFA c-st
  litNFA≅ .inv = toNFA c-st
  litNFA≅ .sec =
    cong (λ z → liftTy ∘⊢ z ∘⊢ lowerTy) (⊗-unit-r∘r⁻ {A = literal c})
  litNFA≅ .ret =
    rec-section TraceTy litAlg toNFA toNFA-homo c-st

  Parse≅ : Parse ≅ LiftTheoryTy ℓlit (literal c)
  Parse≅ = litNFA≅
