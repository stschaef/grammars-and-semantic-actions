{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- NFA trace types: `Accepting` builds only accepting runs; `PotentiallyRejecting`
   indexes by a `Bool`, as a total parse needs.  `Properties` equates them at `true`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Automata.NFA.Base
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Foundations.More using (_⊔ℓ_)
open import Cubical.Relation.Nullary.Base using (Discrete)
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Relation.Nullary.DecidablePropositions.More
open import Cubical.Data.FinSet
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Convolution Alphabet isSetAlphabet

private
  variable ℓN ℓB : Level

ℓ⋆ : Level → Level
ℓ⋆ ℓN = ℓ-max ℓN ℓM

record NFA ℓN : Type (ℓ-suc (ℓ-max ℓN ℓAlph)) where
  field
    Q : FinSet ℓN
    init : ⟨ Q ⟩
    isAcc : ⟨ Q ⟩ → Bool
    transition : FinSet ℓN
    src : ⟨ transition ⟩ → ⟨ Q ⟩
    dst : ⟨ transition ⟩ → ⟨ Q ⟩
    label : ⟨ transition ⟩ → Alphabet
    ε-transition : FinSet ℓN
    ε-src : ⟨ ε-transition ⟩ → ⟨ Q ⟩
    ε-dst : ⟨ ε-transition ⟩ → ⟨ Q ⟩

  decEqQ : Discrete ⟨ Q ⟩
  decEqQ = isFinSet→Discrete (str Q)

  States : Type ℓN
  States = ⟨ Q ⟩

  matchesTransition : Discrete Alphabet → ⟨ transition ⟩
    → States → Alphabet → States → DecProp (ℓ-max ℓN ℓAlph)
  matchesTransition discAlphabet t src' label' dst' =
    DecProp×
      (DecProp≡ (discreteLift (ℓ-max ℓN ℓAlph) discAlphabet)
        (lift label') (lift (label t)))
      (DecProp×
        (DecProp≡ (discreteLift (ℓ-max ℓN ℓAlph) decEqQ)
          (lift src') (lift (src t)))
        (DecProp≡ (discreteLift (ℓ-max ℓN ℓAlph) decEqQ)
          (lift dst') (lift (dst t))))

  hasTransition : Discrete Alphabet
    → States → Alphabet → States → DecProp (ℓ-max ℓN ℓAlph)
  hasTransition discAlphabet src' label' dst' =
    DecProp∃ transition λ t → matchesTransition discAlphabet t src' label' dst'

  -- a silent transition is a bare `Var` summand
  module Accepting where
    data Tag (q : States) : Type ℓN where
      stop : true Eq.≡ isAcc q → Tag q
      step : ∀ t → src t Eq.≡ q → Tag q
      stepε : ∀ t → ε-src t Eq.≡ q → Tag q

    -- `k (Lift εTy)` not `⊗e ε·`: `Lift` has η, so stop branches of
    -- `equalizer-ind` close by `refl`.
    branch : (q : States) → Tag q → Functor (ℓ⋆ ℓN) States (λ _ → tt) tt
    branch q (stop _) = k (LiftTheoryTy ℓN εTy)
    branch q (step t _) =
      ⊗e _⊙_ (two (k (LiftTheoryTy ℓN (literal (label t)))) (Var (dst t)))
    branch q (stepε t _) = Var (ε-dst t)

    TraceTy : (q : States) → Functor (ℓ⋆ ℓN) States (λ _ → tt) tt
    TraceTy q = ⊕e (Tag q) (branch q)

    Trace : (q : States) → TheoryTy (ℓF (ℓ⋆ ℓN) ⊔ℓ ℓN) tt
    Trace = μ TraceTy

    TraceAlg : (States → TheoryTy ℓB tt) → Type _
    TraceAlg A = ∀ q → ⟦ TraceTy q ⟧TheoryTy A ⊢ A q

    -- `⟦⊗e⟧` bridges the code's uncurried convolution and the binary tensor.
    module _ {ℓB} {A : States → TheoryTy ℓB tt} where
      step-out : ∀ {q} (t : ⟨ transition ⟩) (p : src t Eq.≡ q)
        → ⟦ branch q (step t p) ⟧TheoryTy A ⊢ literal (label t) ⊗ A (dst t)
      step-out t p = ⊗-map (lowerTy ∘⊢ lowerTy) lowerTy ∘⊢ ⟦⊗e⟧ _ _

      step-in : ∀ {q} (t : ⟨ transition ⟩) (p : src t Eq.≡ q)
        → literal (label t) ⊗ A (dst t) ⊢ ⟦ branch q (step t p) ⟧TheoryTy A
      step-in t p = ⟦⊗e⟧⁻ _ _ ∘⊢ ⊗-map (liftTy ∘⊢ liftTy) liftTy

      step-η : ∀ {q} t (p : src t Eq.≡ q) → step-in t p ∘⊢ step-out t p ≡ id⊢
      step-η t p = ⟦⊗e⟧-η _ _

    -- `map` at a step summand: `⟦⊗e⟧`-naturality plus η; all a hom proof needs.
    map-step : ∀ {ℓB ℓC} {A : States → TheoryTy ℓB tt}
      {B : States → TheoryTy ℓC tt} (f : ∀ q → A q ⊢ B q)
      {q} (t : ⟨ transition ⟩) (p : src t Eq.≡ q)
      → map (branch q (step t p)) f
        ≡ step-in {A = B} t p ∘⊢ ⊗-map id⊢ (f (dst t)) ∘⊢ step-out {A = A} t p
    map-step {A = A} f t p =
      sym (cong (λ z → map (branch _ (step t p)) f ∘⊢ z) (⟦⊗e⟧-η _ _ {A = A}))
      ∙ cong (λ z → z ∘⊢ ⟦⊗e⟧ {A = A} _ _) (⟦⊗e⟧⁻-nat _ _ f)

    STOP : ∀ {q} → true Eq.≡ isAcc q → εTy ⊢ Trace q
    STOP acc = roll ∘⊢ σ⊕ (stop acc) ∘⊢ liftTy ∘⊢ liftTy

    STEP : ∀ t → literal (label t) ⊗ Trace (dst t) ⊢ Trace (src t)
    STEP t = roll ∘⊢ σ⊕ (step t Eq.refl) ∘⊢ step-in t Eq.refl

    STEPε : ∀ t → Trace (ε-dst t) ⊢ Trace (ε-src t)
    STEPε t = roll ∘⊢ σ⊕ (stepε t Eq.refl) ∘⊢ liftTy

    Parse : TheoryTy _ tt
    Parse = Trace init

  -- `Trace false q` is a rejection certificate, not the absence of a parse.
  module PotentiallyRejecting where
    data Tag : Type ℓN where
      stop step stepε : Tag

    stepBranch : (t : ⟨ transition ⟩) → Functor (ℓ⋆ ℓN) States (λ _ → tt) tt
    stepBranch t =
      ⊗e _⊙_ (two (k (LiftTheoryTy ℓN (literal (label t)))) (Var (dst t)))

    branch : Bool → (q : States) → Tag → Functor (ℓ⋆ ℓN) States (λ _ → tt) tt
    branch b q stop =
      ⊕e (Lift ℓN (b Eq.≡ isAcc q)) λ _ → k (LiftTheoryTy ℓN εTy)
    branch b q step = ⊕e (Eq.fiber src q) λ where
      (t , Eq.refl) → stepBranch t
    branch b q stepε = ⊕e (Eq.fiber ε-src q) λ where
      (t , Eq.refl) → Var (ε-dst t)

    TraceTy : Bool → (q : States) → Functor (ℓ⋆ ℓN) States (λ _ → tt) tt
    TraceTy b q = ⊕e Tag (branch b q)

    Trace : Bool → (q : States) → TheoryTy (ℓF (ℓ⋆ ℓN) ⊔ℓ ℓN) tt
    Trace b = μ (TraceTy b)

    TraceAlg : Bool → (States → TheoryTy ℓB tt) → Type _
    TraceAlg b A = ∀ q → ⟦ TraceTy b q ⟧TheoryTy A ⊢ A q

    module _ {ℓB} {A : States → TheoryTy ℓB tt} where
      step-out : (t : ⟨ transition ⟩)
        → ⟦ stepBranch t ⟧TheoryTy A ⊢ literal (label t) ⊗ A (dst t)
      step-out t = ⊗-map (lowerTy ∘⊢ lowerTy) lowerTy ∘⊢ ⟦⊗e⟧ _ _

      step-in : (t : ⟨ transition ⟩)
        → literal (label t) ⊗ A (dst t) ⊢ ⟦ stepBranch t ⟧TheoryTy A
      step-in t = ⟦⊗e⟧⁻ _ _ ∘⊢ ⊗-map (liftTy ∘⊢ liftTy) liftTy

      step-η : (t : ⟨ transition ⟩) → step-in t ∘⊢ step-out t ≡ id⊢
      step-η t = ⟦⊗e⟧-η _ _

    map-step : ∀ {ℓB ℓC} {A : States → TheoryTy ℓB tt}
      {B : States → TheoryTy ℓC tt} (f : ∀ q → A q ⊢ B q)
      (t : ⟨ transition ⟩)
      → map (stepBranch t) f
        ≡ step-in {A = B} t ∘⊢ ⊗-map id⊢ (f (dst t)) ∘⊢ step-out {A = A} t
    map-step {A = A} f t =
      sym (cong (λ z → map (stepBranch t) f ∘⊢ z) (⟦⊗e⟧-η _ _ {A = A}))
      ∙ cong (λ z → z ∘⊢ ⟦⊗e⟧ {A = A} _ _) (⟦⊗e⟧⁻-nat _ _ f)

    STOP : ∀ {b q} → b Eq.≡ isAcc q → εTy ⊢ Trace b q
    STOP acc = roll ∘⊢ σ⊕ stop ∘⊢ σ⊕ (lift acc) ∘⊢ liftTy ∘⊢ liftTy

    STEP : ∀ b (t : ⟨ transition ⟩)
      → literal (label t) ⊗ Trace b (dst t) ⊢ Trace b (src t)
    STEP b t = roll ∘⊢ σ⊕ step ∘⊢ σ⊕ (t , Eq.refl) ∘⊢ step-in t

    STEPε : ∀ b (t : ⟨ ε-transition ⟩)
      → Trace b (ε-dst t) ⊢ Trace b (ε-src t)
    STEPε b t = roll ∘⊢ σ⊕ stepε ∘⊢ σ⊕ (t , Eq.refl) ∘⊢ liftTy

    Parse : TheoryTy _ tt
    Parse = Trace true init
