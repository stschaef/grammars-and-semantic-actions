{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Thompson's construction at `⊕`: a fresh initial state with a silent
   transition into each of the two automata.

   Both round trips are `rec-section`: `toNFA` and `fromNFA` are algebra maps,
   and at a labelled transition that is `map-step`, at a silent one it is the
   `Var` summand's lift, and at a stop it is `refl`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.WildCat.LocallySmall.Base
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Thompson.Construction.Sum
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.Properties using (isFinSetUnit ; EquivPresIsFinSet)
open import Cubical.Data.Bool using (false)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Sum as Sum
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Automata.NFA.Base Alphabet isSetAlphabet

open WildCatNotation
open WildCatIso
open Iso
open NFA

private variable ℓN ℓN' : Level

module _ (N : NFA ℓN) (N' : NFA ℓN') where
  private
    module A = NFA.Accepting N
    module A' = NFA.Accepting N'

  data ⊕State : Type (ℓ-max ℓN ℓN') where
    start : ⊕State
    inl' : ⟨ N .Q ⟩ → ⊕State
    inr' : ⟨ N' .Q ⟩ → ⊕State

  ⊕State-rep : ⊕State ≃ (Unit Sum.⊎ (⟨ N .Q ⟩ Sum.⊎ ⟨ N' .Q ⟩))
  ⊕State-rep = isoToEquiv (iso to from tf ft)
    where
    to : ⊕State → Unit Sum.⊎ (⟨ N .Q ⟩ Sum.⊎ ⟨ N' .Q ⟩)
    to start = Sum.inl tt
    to (inl' x) = Sum.inr (Sum.inl x)
    to (inr' x) = Sum.inr (Sum.inr x)

    from : Unit Sum.⊎ (⟨ N .Q ⟩ Sum.⊎ ⟨ N' .Q ⟩) → ⊕State
    from (Sum.inl _) = start
    from (Sum.inr (Sum.inl x)) = inl' x
    from (Sum.inr (Sum.inr x)) = inr' x

    tf : ∀ y → to (from y) ≡ y
    tf (Sum.inl _) = refl
    tf (Sum.inr (Sum.inl x)) = refl
    tf (Sum.inr (Sum.inr x)) = refl

    ft : ∀ q → from (to q) ≡ q
    ft start = refl
    ft (inl' x) = refl
    ft (inr' x) = refl

  ⊕Trans : FinSet (ℓ-max ℓN ℓN')
  ⊕Trans .fst = ⟨ N .transition ⟩ Sum.⊎ ⟨ N' .transition ⟩
  ⊕Trans .snd = isFinSet⊎ (N .transition) (N' .transition)

  data ⊕εTrans : Type (ℓ-max ℓN ℓN') where
    pick-inl pick-inr : ⊕εTrans
    N-ε-trans : ⟨ N .ε-transition ⟩ → ⊕εTrans
    N'-ε-trans : ⟨ N' .ε-transition ⟩ → ⊕εTrans

  ⊕εTrans-rep :
    (Unit Sum.⊎ (Unit Sum.⊎ (⟨ N .ε-transition ⟩ Sum.⊎ ⟨ N' .ε-transition ⟩)))
    ≃ ⊕εTrans
  ⊕εTrans-rep = isoToEquiv (iso to from tf ft)
    where
    Src = Unit Sum.⊎ (Unit Sum.⊎ (⟨ N .ε-transition ⟩ Sum.⊎ ⟨ N' .ε-transition ⟩))

    to : Src → ⊕εTrans
    to (Sum.inl _) = pick-inl
    to (Sum.inr (Sum.inl _)) = pick-inr
    to (Sum.inr (Sum.inr (Sum.inl t))) = N-ε-trans t
    to (Sum.inr (Sum.inr (Sum.inr t'))) = N'-ε-trans t'

    from : ⊕εTrans → Src
    from pick-inl = Sum.inl tt
    from pick-inr = Sum.inr (Sum.inl tt)
    from (N-ε-trans t) = Sum.inr (Sum.inr (Sum.inl t))
    from (N'-ε-trans t') = Sum.inr (Sum.inr (Sum.inr t'))

    tf : ∀ y → to (from y) ≡ y
    tf pick-inl = refl
    tf pick-inr = refl
    tf (N-ε-trans t) = refl
    tf (N'-ε-trans t') = refl

    ft : ∀ y → from (to y) ≡ y
    ft (Sum.inl _) = refl
    ft (Sum.inr (Sum.inl _)) = refl
    ft (Sum.inr (Sum.inr (Sum.inl t))) = refl
    ft (Sum.inr (Sum.inr (Sum.inr t'))) = refl

  ⊕NFA : NFA (ℓ-max ℓN ℓN')
  ⊕NFA .Q = ⊕State , EquivPresIsFinSet (invEquiv ⊕State-rep)
    (isFinSet⊎ (_ , isFinSetUnit) (_ , isFinSet⊎ (N .Q) (N' .Q)))
  ⊕NFA .init = start
  ⊕NFA .isAcc start = false
  ⊕NFA .isAcc (inl' q) = N .isAcc q
  ⊕NFA .isAcc (inr' q') = N' .isAcc q'
  ⊕NFA .transition = ⊕Trans
  ⊕NFA .src (Sum.inl t) = inl' (N .src t)
  ⊕NFA .src (Sum.inr t') = inr' (N' .src t')
  ⊕NFA .dst (Sum.inl t) = inl' (N .dst t)
  ⊕NFA .dst (Sum.inr t') = inr' (N' .dst t')
  ⊕NFA .label (Sum.inl t) = N .label t
  ⊕NFA .label (Sum.inr t') = N' .label t'
  ⊕NFA .ε-transition = ⊕εTrans , EquivPresIsFinSet ⊕εTrans-rep
    (isFinSet⊎ (_ , isFinSetUnit)
      (_ , isFinSet⊎ (_ , isFinSetUnit)
        (_ , isFinSet⊎ (N .ε-transition) (N' .ε-transition))))
  ⊕NFA .ε-src pick-inl = start
  ⊕NFA .ε-src pick-inr = start
  ⊕NFA .ε-src (N-ε-trans t) = inl' (N .ε-src t)
  ⊕NFA .ε-src (N'-ε-trans t') = inr' (N' .ε-src t')
  ⊕NFA .ε-dst pick-inl = inl' (N .init)
  ⊕NFA .ε-dst pick-inr = inr' (N' .init)
  ⊕NFA .ε-dst (N-ε-trans t) = inl' (N .ε-dst t)
  ⊕NFA .ε-dst (N'-ε-trans t') = inr' (N' .ε-dst t')

  open NFA.Accepting ⊕NFA

  ℓ⊕ : Level
  ℓ⊕ = ℓ-max (ℓF (ℓ⋆ (ℓ-max ℓN ℓN'))) (ℓ-max ℓN ℓN')

  ⟦_⟧⊕ : ⊕State → TheoryTy ℓ⊕ tt
  ⟦ start ⟧⊕ = A.Parse ⊕ A'.Parse
  ⟦ inl' q ⟧⊕ = LiftTheoryTy ℓ⊕ (A.Trace q)
  ⟦ inr' q' ⟧⊕ = LiftTheoryTy ℓ⊕ (A'.Trace q')

  ⊕Alg : TraceAlg ⟦_⟧⊕
  ⊕Alg start = ⊕ᴰ-elim λ where
    (step (Sum.inl t) ())
    (step (Sum.inr t) ())
    (stepε pick-inl Eq.refl) → inl ∘⊢ lowerTy ∘⊢ lowerTy
    (stepε pick-inr Eq.refl) → inr ∘⊢ lowerTy ∘⊢ lowerTy
  ⊕Alg (inl' q) = ⊕ᴰ-elim λ where
    (stop acc) → liftTy ∘⊢ A.STOP acc ∘⊢ lowerTy ∘⊢ lowerTy
    (step (Sum.inl t) Eq.refl) →
      liftTy ∘⊢ A.STEP t ∘⊢ ⊗-map id⊢ lowerTy
        ∘⊢ step-out (Sum.inl t) Eq.refl
    (stepε (N-ε-trans t) Eq.refl) →
      liftTy ∘⊢ A.STEPε t ∘⊢ lowerTy ∘⊢ lowerTy
  ⊕Alg (inr' q') = ⊕ᴰ-elim λ where
    (stop acc) → liftTy ∘⊢ A'.STOP acc ∘⊢ lowerTy ∘⊢ lowerTy
    (step (Sum.inr t) Eq.refl) →
      liftTy ∘⊢ A'.STEP t ∘⊢ ⊗-map id⊢ lowerTy
        ∘⊢ step-out (Sum.inr t) Eq.refl
    (stepε (N'-ε-trans t) Eq.refl) →
      liftTy ∘⊢ A'.STEPε t ∘⊢ lowerTy ∘⊢ lowerTy

  fromNFA : ∀ q → Trace q ⊢ ⟦ q ⟧⊕
  fromNFA = rec TraceTy ⊕Alg

  -- each sub-automaton's trace embeds by renaming transitions
  ⟦_⟧N : ⟨ N .Q ⟩ → TheoryTy ℓ⊕ tt
  ⟦ q ⟧N = Trace (inl' q)

  ⟦_⟧N' : ⟨ N' .Q ⟩ → TheoryTy ℓ⊕ tt
  ⟦ q' ⟧N' = Trace (inr' q')

  NAlg : A.TraceAlg ⟦_⟧N
  NAlg q = ⊕ᴰ-elim λ where
    (stop acc) → STOP acc ∘⊢ lowerTy ∘⊢ lowerTy
    (step t Eq.refl) →
      STEP (Sum.inl t) ∘⊢ A.step-out t Eq.refl
    (stepε t Eq.refl) → STEPε (N-ε-trans t) ∘⊢ lowerTy

  N→⊕NFA : ∀ q → A.Trace q ⊢ ⟦ q ⟧N
  N→⊕NFA = rec A.TraceTy NAlg

  N'Alg : A'.TraceAlg ⟦_⟧N'
  N'Alg q' = ⊕ᴰ-elim λ where
    (stop acc) → STOP acc ∘⊢ lowerTy ∘⊢ lowerTy
    (step t Eq.refl) →
      STEP (Sum.inr t) ∘⊢ A'.step-out t Eq.refl
    (stepε t Eq.refl) → STEPε (N'-ε-trans t) ∘⊢ lowerTy

  N'→⊕NFA : ∀ q' → A'.Trace q' ⊢ ⟦ q' ⟧N'
  N'→⊕NFA = rec A'.TraceTy N'Alg

  toNFA : ∀ q → ⟦ q ⟧⊕ ⊢ Trace q
  toNFA start =
    ⊕-elim (STEPε pick-inl ∘⊢ N→⊕NFA (N .init))
           (STEPε pick-inr ∘⊢ N'→⊕NFA (N' .init))
  toNFA (inl' q) = N→⊕NFA q ∘⊢ lowerTy
  toNFA (inr' q') = N'→⊕NFA q' ∘⊢ lowerTy

  private
    -- The composite each `step` branch of the homomorphism law unfolds to,
    -- with `z` the `map` that `map-step` rewrites.
    stepN-comp : (t : ⟨ N .transition ⟩)
      → (⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy A.Trace
        ⊢ ⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy ⟦_⟧N)
      → ⟦ branch (inl' (N .src t)) (step (Sum.inl t) Eq.refl) ⟧TheoryTy ⟦_⟧⊕
        ⊢ Trace (inl' (N .src t))
    stepN-comp t z =
      STEP (Sum.inl t) ∘⊢ A.step-out t Eq.refl ∘⊢ z ∘⊢ A.step-in t Eq.refl
        ∘⊢ ⊗-map id⊢ lowerTy ∘⊢ step-out (Sum.inl t) Eq.refl

    stepN'-comp : (t : ⟨ N' .transition ⟩)
      → (⟦ A'.branch (N' .src t) (A'.step t Eq.refl) ⟧TheoryTy A'.Trace
        ⊢ ⟦ A'.branch (N' .src t) (A'.step t Eq.refl) ⟧TheoryTy ⟦_⟧N')
      → ⟦ branch (inr' (N' .src t)) (step (Sum.inr t) Eq.refl) ⟧TheoryTy ⟦_⟧⊕
        ⊢ Trace (inr' (N' .src t))
    stepN'-comp t z =
      STEP (Sum.inr t) ∘⊢ A'.step-out t Eq.refl ∘⊢ z ∘⊢ A'.step-in t Eq.refl
        ∘⊢ ⊗-map id⊢ lowerTy ∘⊢ step-out (Sum.inr t) Eq.refl

    roll-step : ∀ (t : ⟨ ⊕Trans ⟩)
      → (⟦ branch (⊕NFA .src t) (step t Eq.refl) ⟧TheoryTy ⟦_⟧⊕
        ⊢ ⟦ branch (⊕NFA .src t) (step t Eq.refl) ⟧TheoryTy Trace)
      → ⟦ branch (⊕NFA .src t) (step t Eq.refl) ⟧TheoryTy ⟦_⟧⊕
        ⊢ Trace (⊕NFA .src t)
    roll-step t z = roll ∘⊢ σ⊕ (step t Eq.refl) ∘⊢ z

  -- `toNFA` is an algebra map.  Every branch but a labelled transition is
  -- `refl`; that one is `map-step` on each side.
  toNFA-homo : ∀ q → toNFA q ∘⊢ ⊕Alg q ≡ roll ∘⊢ map (TraceTy q) toNFA
  toNFA-homo start = ⊕ᴰ≡ _ _ λ where
    (step (Sum.inl t) ())
    (step (Sum.inr t) ())
    (stepε pick-inl Eq.refl) → refl
    (stepε pick-inr Eq.refl) → refl
  toNFA-homo (inl' q) = ⊕ᴰ≡ _ _ λ where
    (stop acc) → refl
    (step (Sum.inl t) Eq.refl) →
      cong (stepN-comp t) (A.map-step N→⊕NFA t Eq.refl)
      ∙ cong (roll-step (Sum.inl t)) (sym (map-step toNFA (Sum.inl t) Eq.refl))
    (stepε (N-ε-trans t) Eq.refl) → refl
  toNFA-homo (inr' q') = ⊕ᴰ≡ _ _ λ where
    (stop acc) → refl
    (step (Sum.inr t) Eq.refl) →
      cong (stepN'-comp t) (A'.map-step N'→⊕NFA t Eq.refl)
      ∙ cong (roll-step (Sum.inr t)) (sym (map-step toNFA (Sum.inr t) Eq.refl))
    (stepε (N'-ε-trans t) Eq.refl) → refl

  -- `fromNFA`, read as a map out of each sub-automaton's trace.  `rec-section`
  -- at `N` then says the round trip through `⊕NFA` is the identity on `N`'s
  -- traces.
  private
    fromN : ∀ q → ⟦ q ⟧N ⊢ A.Trace q
    fromN q = lowerTy ∘⊢ fromNFA (inl' q)

    fromN' : ∀ q' → ⟦ q' ⟧N' ⊢ A'.Trace q'
    fromN' q' = lowerTy ∘⊢ fromNFA (inr' q')

    stepN-comp⁻ : (t : ⟨ N .transition ⟩)
      → (⟦ branch (inl' (N .src t)) (step (Sum.inl t) Eq.refl) ⟧TheoryTy Trace
        ⊢ ⟦ branch (inl' (N .src t)) (step (Sum.inl t) Eq.refl) ⟧TheoryTy ⟦_⟧⊕)
      → ⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy ⟦_⟧N
        ⊢ A.Trace (N .src t)
    stepN-comp⁻ t z =
      A.STEP t ∘⊢ ⊗-map id⊢ lowerTy ∘⊢ step-out (Sum.inl t) Eq.refl ∘⊢ z
        ∘⊢ step-in (Sum.inl t) Eq.refl ∘⊢ A.step-out t Eq.refl

    stepN'-comp⁻ : (t : ⟨ N' .transition ⟩)
      → (⟦ branch (inr' (N' .src t)) (step (Sum.inr t) Eq.refl) ⟧TheoryTy Trace
        ⊢ ⟦ branch (inr' (N' .src t)) (step (Sum.inr t) Eq.refl) ⟧TheoryTy ⟦_⟧⊕)
      → ⟦ A'.branch (N' .src t) (A'.step t Eq.refl) ⟧TheoryTy ⟦_⟧N'
        ⊢ A'.Trace (N' .src t)
    stepN'-comp⁻ t z =
      A'.STEP t ∘⊢ ⊗-map id⊢ lowerTy ∘⊢ step-out (Sum.inr t) Eq.refl ∘⊢ z
        ∘⊢ step-in (Sum.inr t) Eq.refl ∘⊢ A'.step-out t Eq.refl

    rollN-step : (t : ⟨ N .transition ⟩)
      → (⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy ⟦_⟧N
        ⊢ ⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy A.Trace)
      → ⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy ⟦_⟧N
        ⊢ A.Trace (N .src t)
    rollN-step t z = roll ∘⊢ σ⊕ (A.step t Eq.refl) ∘⊢ z

    rollN'-step : (t : ⟨ N' .transition ⟩)
      → (⟦ A'.branch (N' .src t) (A'.step t Eq.refl) ⟧TheoryTy ⟦_⟧N'
        ⊢ ⟦ A'.branch (N' .src t) (A'.step t Eq.refl) ⟧TheoryTy A'.Trace)
      → ⟦ A'.branch (N' .src t) (A'.step t Eq.refl) ⟧TheoryTy ⟦_⟧N'
        ⊢ A'.Trace (N' .src t)
    rollN'-step t z = roll ∘⊢ σ⊕ (A'.step t Eq.refl) ∘⊢ z

  fromN-homo : ∀ q → fromN q ∘⊢ NAlg q ≡ roll ∘⊢ map (A.TraceTy q) fromN
  fromN-homo q = ⊕ᴰ≡ _ _ λ where
    (A.stop acc) → refl
    (A.step t Eq.refl) →
      cong (stepN-comp⁻ t) (map-step fromNFA (Sum.inl t) Eq.refl)
      ∙ cong (rollN-step t) (sym (A.map-step fromN t Eq.refl))
    (A.stepε t Eq.refl) → refl

  fromN'-homo : ∀ q' → fromN' q' ∘⊢ N'Alg q' ≡ roll ∘⊢ map (A'.TraceTy q') fromN'
  fromN'-homo q' = ⊕ᴰ≡ _ _ λ where
    (A'.stop acc) → refl
    (A'.step t Eq.refl) →
      cong (stepN'-comp⁻ t) (map-step fromNFA (Sum.inr t) Eq.refl)
      ∙ cong (rollN'-step t) (sym (A'.map-step fromN' t Eq.refl))
    (A'.stepε t Eq.refl) → refl

  fromN-section : ∀ q → fromN q ∘⊢ N→⊕NFA q ≡ id⊢
  fromN-section = rec-section A.TraceTy NAlg fromN fromN-homo

  fromN'-section : ∀ q' → fromN' q' ∘⊢ N'→⊕NFA q' ≡ id⊢
  fromN'-section = rec-section A'.TraceTy N'Alg fromN' fromN'-homo

  private
    inl⊕ : A.Parse ⊢ (A.Parse ⊕ A'.Parse)
    inl⊕ = inl

    inr⊕ : A'.Parse ⊢ (A.Parse ⊕ A'.Parse)
    inr⊕ = inr

  ⊕NFA≅ : Parse ≅ (A.Parse ⊕ A'.Parse)
  ⊕NFA≅ .fun = fromNFA start
  ⊕NFA≅ .inv = toNFA start
  ⊕NFA≅ .ret = rec-section TraceTy ⊕Alg toNFA toNFA-homo start
  ⊕NFA≅ .sec = ⊕≡ _ _
    (cong (inl⊕ ∘⊢_) (fromN-section (N .init)))
    (cong (inr⊕ ∘⊢_) (fromN'-section (N' .init)))
