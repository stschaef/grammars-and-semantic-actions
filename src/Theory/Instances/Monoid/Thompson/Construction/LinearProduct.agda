{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Thompson's construction at `⊗`: the two automata side by side, with a
   silent transition out of each of `N`'s accepting states into `N'`'s start.

   The state where the run crosses over is not determined by the input, so
   the map back is written with the residual: `N`'s trace is folded into
   "a `⊗NFA` trace still owing an `N'` trace", and the crossing spends it. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.WildCat.LocallySmall.Base
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Thompson.Construction.LinearProduct
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Relation.Nullary.Base using (Dec)
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Relation.Nullary.DecidablePropositions.More
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.FinSet.Properties using (isFinSetBool ; EquivPresIsFinSet)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Sum as Sum
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (_⟜_ ; ⟜-intro ; ⟜-intro⁻ ; ⟜-app ; ⟜-β ; ⟜-η ; ⟜-post ; ⟜-precomp
        ; ⊗ε-unit-l⁻)
open import Theory.Instances.Monoid.Residual.Laws Alphabet isSetAlphabet
  using (⟜-post-precomp-intro⁻)
open import Theory.Instances.Monoid.Unitor Alphabet isSetAlphabet
  using (⊗-assoc⁻∘⊗-assoc ; ⊗-assoc∘⊗-assoc⁻ ; ⊗-unit-l∘l⁻ ; ⊗-unit-l⁻∘l ; ⊗-unit-l-nat↑ ; ⊗-assoc-nat↑ ; ⊗-assoc⁻-nat↑)
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

  ⊗State : FinSet (ℓ-max ℓN ℓN')
  ⊗State .fst = ⟨ N .Q ⟩ Sum.⊎ ⟨ N' .Q ⟩
  ⊗State .snd = isFinSet⊎ (N .Q) (N' .Q)

  ⊗Trans : FinSet (ℓ-max ℓN ℓN')
  ⊗Trans .fst = ⟨ N .transition ⟩ Sum.⊎ ⟨ N' .transition ⟩
  ⊗Trans .snd = isFinSet⊎ (N .transition) (N' .transition)

  data ⊗εTrans : Type (ℓ-max ℓN ℓN') where
    N-acc : ∀ q → true Eq.≡ N .isAcc q → ⊗εTrans
    N-ε-trans : ⟨ N .ε-transition ⟩ → ⊗εTrans
    N'-ε-trans : ⟨ N' .ε-transition ⟩ → ⊗εTrans

  ⊗εTrans-rep :
    ((Σ[ q ∈ ⟨ N .Q ⟩ ] (true Eq.≡ N .isAcc q))
      Sum.⊎ (⟨ N .ε-transition ⟩ Sum.⊎ ⟨ N' .ε-transition ⟩))
    ≃ ⊗εTrans
  ⊗εTrans-rep = isoToEquiv (iso to from tf ft)
    where
    Src = (Σ[ q ∈ ⟨ N .Q ⟩ ] (true Eq.≡ N .isAcc q))
      Sum.⊎ (⟨ N .ε-transition ⟩ Sum.⊎ ⟨ N' .ε-transition ⟩)

    to : Src → ⊗εTrans
    to (Sum.inl (q , acc)) = N-acc q acc
    to (Sum.inr (Sum.inl t)) = N-ε-trans t
    to (Sum.inr (Sum.inr t')) = N'-ε-trans t'

    from : ⊗εTrans → Src
    from (N-acc q acc) = Sum.inl (q , acc)
    from (N-ε-trans t) = Sum.inr (Sum.inl t)
    from (N'-ε-trans t') = Sum.inr (Sum.inr t')

    tf : ∀ y → to (from y) ≡ y
    tf (N-acc q acc) = refl
    tf (N-ε-trans t) = refl
    tf (N'-ε-trans t') = refl

    ft : ∀ y → from (to y) ≡ y
    ft (Sum.inl _) = refl
    ft (Sum.inr (Sum.inl _)) = refl
    ft (Sum.inr (Sum.inr _)) = refl

  ⊗NFA : NFA (ℓ-max ℓN ℓN')
  ⊗NFA .Q = ⊗State
  ⊗NFA .init = Sum.inl (N .init)
  ⊗NFA .isAcc (Sum.inl q) = false
  ⊗NFA .isAcc (Sum.inr q') = N' .isAcc q'
  ⊗NFA .transition = ⊗Trans
  ⊗NFA .src (Sum.inl t) = Sum.inl (N .src t)
  ⊗NFA .src (Sum.inr t') = Sum.inr (N' .src t')
  ⊗NFA .dst (Sum.inl t) = Sum.inl (N .dst t)
  ⊗NFA .dst (Sum.inr t') = Sum.inr (N' .dst t')
  ⊗NFA .label (Sum.inl t) = N .label t
  ⊗NFA .label (Sum.inr t') = N' .label t'
  ⊗NFA .ε-transition .fst = ⊗εTrans
  ⊗NFA .ε-transition .snd = EquivPresIsFinSet ⊗εTrans-rep
    (isFinSet⊎
      (_ , isFinSetΣ (N .Q) λ q →
        _ , isDecProp→isFinSet (the-dec-prop q .fst .snd) (the-dec-prop q .snd))
      (_ , isFinSet⊎ (N .ε-transition) (N' .ε-transition)))
    where
    the-dec-prop : ⟨ N .Q ⟩ → Σ (hProp ℓ-zero) λ P → Dec (P .fst)
    the-dec-prop q = isFinSet→DecProp-Eq≡ isFinSetBool true (N .isAcc q)
  ⊗NFA .ε-src (N-acc q _) = Sum.inl q
  ⊗NFA .ε-src (N-ε-trans t) = Sum.inl (N .ε-src t)
  ⊗NFA .ε-src (N'-ε-trans t') = Sum.inr (N' .ε-src t')
  ⊗NFA .ε-dst (N-acc _ _) = Sum.inr (N' .init)
  ⊗NFA .ε-dst (N-ε-trans t) = Sum.inl (N .ε-dst t)
  ⊗NFA .ε-dst (N'-ε-trans t') = Sum.inr (N' .ε-dst t')

  open NFA.Accepting ⊗NFA

  ℓ⊗ : Level
  ℓ⊗ = ℓ-max (ℓF (ℓ⋆ (ℓ-max ℓN ℓN'))) (ℓ-max ℓN ℓN')

  -- What is still owed from a state: at `N`'s side, the rest of `N`'s parse
  -- *and* the whole of `N'`'s; at `N'`'s side, just `N'`'s.
  ⟦_⟧⊗ : ⟨ ⊗State ⟩ → TheoryTy ℓ⊗ tt
  ⟦ Sum.inl q ⟧⊗ = A.Trace q ⊗ A'.Parse
  ⟦ Sum.inr q' ⟧⊗ = LiftTheoryTy ℓ⊗ (A'.Trace q')

  ⊗Alg : TraceAlg ⟦_⟧⊗
  ⊗Alg (Sum.inl q) = ⊕ᴰ-elim λ where
    (stop ())
    (step (Sum.inl t) Eq.refl) →
      ⊗-map (A.STEP t) id⊢ ∘⊢ ⊗-assoc⁻ ∘⊢ step-out (Sum.inl t) Eq.refl
    (step (Sum.inr t) ())
    (stepε (N-acc _ acc) Eq.refl) →
      ⊗-map (A.STOP acc) id⊢ ∘⊢ ⊗ε-unit-l⁻ ∘⊢ lowerTy ∘⊢ lowerTy
    (stepε (N-ε-trans t) Eq.refl) → ⊗-map (A.STEPε t) id⊢ ∘⊢ lowerTy
    (stepε (N'-ε-trans t) ())
  ⊗Alg (Sum.inr q') = ⊕ᴰ-elim λ where
    (stop acc) → liftTy ∘⊢ A'.STOP acc ∘⊢ lowerTy ∘⊢ lowerTy
    (step (Sum.inl t) ())
    (step (Sum.inr t) Eq.refl) →
      liftTy ∘⊢ A'.STEP t ∘⊢ ⊗-map id⊢ lowerTy
        ∘⊢ step-out (Sum.inr t) Eq.refl
    (stepε (N-acc _ _) ())
    (stepε (N-ε-trans t) ())
    (stepε (N'-ε-trans t) Eq.refl) →
      liftTy ∘⊢ A'.STEPε t ∘⊢ lowerTy ∘⊢ lowerTy

  fromNFA : ∀ q → Trace q ⊢ ⟦ q ⟧⊗
  fromNFA = rec TraceTy ⊗Alg

  ⟦_⟧N' : ⟨ N' .Q ⟩ → TheoryTy ℓ⊗ tt
  ⟦ q' ⟧N' = Trace (Sum.inr q')

  N'Alg : A'.TraceAlg ⟦_⟧N'
  N'Alg q' = ⊕ᴰ-elim λ where
    (A'.stop acc) → STOP acc ∘⊢ lowerTy ∘⊢ lowerTy
    (A'.step t Eq.refl) → STEP (Sum.inr t) ∘⊢ A'.step-out t Eq.refl
    (A'.stepε t Eq.refl) → STEPε (N'-ε-trans t) ∘⊢ lowerTy

  N'→⊗NFA : ∀ q' → A'.Trace q' ⊢ ⟦ q' ⟧N'
  N'→⊗NFA = rec A'.TraceTy N'Alg

  -- `N`'s trace becomes a `⊗NFA` trace *still owing* an `N'` parse.  The
  -- residual is where the nondeterminism of the crossover goes.
  ⟦_⟧N : ⟨ N .Q ⟩ → TheoryTy ℓ⊗ tt
  ⟦ q ⟧N = Trace (Sum.inl q) ⟜ Trace (Sum.inr (N' .init))

  NAlg : A.TraceAlg ⟦_⟧N
  NAlg q = ⊕ᴰ-elim λ where
    (A.stop acc) →
      ⟜-intro (STEPε (N-acc q acc) ∘⊢ ⊗-unit-l
                ∘⊢ ⊗-map (lowerTy ∘⊢ lowerTy) id⊢)
    (A.step t Eq.refl) →
      ⟜-intro (STEP (Sum.inl t) ∘⊢ ⊗-map id⊢ ⟜-app ∘⊢ ⊗-assoc
                ∘⊢ ⊗-map (A.step-out t Eq.refl) id⊢)
    (A.stepε t Eq.refl) →
      ⟜-intro (STEPε (N-ε-trans t) ∘⊢ ⟜-app ∘⊢ ⊗-map lowerTy id⊢)

  N→⟜ : ∀ q → A.Trace q ⊢ ⟦ q ⟧N
  N→⟜ = rec A.TraceTy NAlg

  N→⊗NFA : ∀ q → A.Trace q ⊗ A'.Parse ⊢ Trace (Sum.inl q)
  N→⊗NFA q = ⟜-intro⁻ (N→⟜ q) ∘⊢ ⊗-map id⊢ (N'→⊗NFA (N' .init))

  -- One `rec-section` covers both `⊗NFA` states at once: `equalizer-ind`
  -- forces a carrier at *every* state, a homomorphism law does not.
  gmap : ∀ q → ⟦ q ⟧⊗ ⊢ Trace q
  gmap (Sum.inl q) = N→⊗NFA q
  gmap (Sum.inr q') = N'→⊗NFA q' ∘⊢ lowerTy

  private
    P' : A'.Parse ⊢ Trace (Sum.inr (N' .init))
    P' = N'→⊗NFA (N' .init)

    -- The three bodies `NAlg` curries.  `⟜-β` is the only non-definitional
    -- step in each branch, and it needs the body written out.
    W-acc : ∀ q (acc : true Eq.≡ N .isAcc q)
      → εTy ⊗ Trace (Sum.inr (N' .init)) ⊢ Trace (Sum.inl q)
    W-acc q acc = STEPε (N-acc q acc) ∘⊢ ⊗-unit-l

    W-ε : (t : ⟨ N .ε-transition ⟩)
      → A.Trace (N .ε-dst t) ⊗ Trace (Sum.inr (N' .init))
      ⊢ Trace (Sum.inl (N .ε-src t))
    W-ε t = STEPε (N-ε-trans t) ∘⊢ ⟜-app ∘⊢ ⊗-map (N→⟜ (N .ε-dst t)) id⊢

    W-step : (t : ⟨ N .transition ⟩)
      → (literal (N .label t) ⊗ A.Trace (N .dst t)) ⊗ Trace (Sum.inr (N' .init))
      ⊢ Trace (Sum.inl (N .src t))
    W-step t = STEP (Sum.inl t) ∘⊢ ⊗-map id⊢ ⟜-app ∘⊢ ⊗-assoc
      ∘⊢ ⊗-map (⊗-map id⊢ (N→⟜ (N .dst t))) id⊢

    tail-acc : ∀ q (acc : true Eq.≡ N .isAcc q)
      → (εTy ⊗ Trace (Sum.inr (N' .init)) ⊢ Trace (Sum.inl q))
      → ⟦ branch (Sum.inl q) (stepε (N-acc q acc) Eq.refl) ⟧TheoryTy ⟦_⟧⊗
      ⊢ Trace (Sum.inl q)
    tail-acc q acc z =
      z ∘⊢ ⊗-map id⊢ P' ∘⊢ ⊗ε-unit-l⁻ ∘⊢ lowerTy ∘⊢ lowerTy

    accL : ∀ q (acc : true Eq.≡ N .isAcc q)
      → (εTy ⊗ A'.Parse ⊢ Trace (Sum.inr (N' .init)))
      → ⟦ branch (Sum.inl q) (stepε (N-acc q acc) Eq.refl) ⟧TheoryTy ⟦_⟧⊗
      ⊢ Trace (Sum.inl q)
    accL q acc z = STEPε (N-acc q acc) ∘⊢ z ∘⊢ ⊗ε-unit-l⁻ ∘⊢ lowerTy ∘⊢ lowerTy

    accR : ∀ q (acc : true Eq.≡ N .isAcc q)
      → (A'.Parse ⊢ A'.Parse)
      → ⟦ branch (Sum.inl q) (stepε (N-acc q acc) Eq.refl) ⟧TheoryTy ⟦_⟧⊗
      ⊢ Trace (Sum.inl q)
    accR q acc z = STEPε (N-acc q acc) ∘⊢ P' ∘⊢ z ∘⊢ lowerTy ∘⊢ lowerTy

    tail-ε : (t : ⟨ N .ε-transition ⟩)
      → (A.Trace (N .ε-dst t) ⊗ Trace (Sum.inr (N' .init))
        ⊢ Trace (Sum.inl (N .ε-src t)))
      → ⟦ branch (Sum.inl (N .ε-src t)) (stepε (N-ε-trans t) Eq.refl) ⟧TheoryTy ⟦_⟧⊗
      ⊢ Trace (Sum.inl (N .ε-src t))
    tail-ε t z = z ∘⊢ ⊗-map id⊢ P' ∘⊢ lowerTy

    NAlg-step : (t : ⟨ N .transition ⟩)
      → ⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy ⟦_⟧N ⊢ ⟦ N .src t ⟧N
    NAlg-step t = ⟜-intro (STEP (Sum.inl t) ∘⊢ ⊗-map id⊢ ⟜-app ∘⊢ ⊗-assoc
      ∘⊢ ⊗-map (A.step-out t Eq.refl) id⊢)

    lhs-step : (t : ⟨ N .transition ⟩)
      → (⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy A.Trace
        ⊢ ⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy ⟦_⟧N)
      → ⟦ branch (Sum.inl (N .src t)) (step (Sum.inl t) Eq.refl) ⟧TheoryTy ⟦_⟧⊗
        ⊢ Trace (Sum.inl (N .src t))
    lhs-step t z =
      ⟜-intro⁻ (NAlg-step t ∘⊢ z ∘⊢ A.step-in t Eq.refl)
        ∘⊢ ⊗-map id⊢ P' ∘⊢ ⊗-assoc⁻ ∘⊢ step-out (Sum.inl t) Eq.refl

    mid-step : (t : ⟨ N .transition ⟩)
      → (literal (N .label t) ⊗ (A.Trace (N .dst t) ⊗ A'.Parse)
        ⊢ literal (N .label t) ⊗ (A.Trace (N .dst t) ⊗ A'.Parse))
      → ⟦ branch (Sum.inl (N .src t)) (step (Sum.inl t) Eq.refl) ⟧TheoryTy ⟦_⟧⊗
        ⊢ Trace (Sum.inl (N .src t))
    mid-step t z = STEP (Sum.inl t) ∘⊢ ⊗-map id⊢ (N→⊗NFA (N .dst t)) ∘⊢ z
      ∘⊢ step-out (Sum.inl t) Eq.refl

    tail-step : (t : ⟨ N .transition ⟩)
      → ((literal (N .label t) ⊗ A.Trace (N .dst t))
        ⊗ Trace (Sum.inr (N' .init)) ⊢ Trace (Sum.inl (N .src t)))
      → ⟦ branch (Sum.inl (N .src t)) (step (Sum.inl t) Eq.refl) ⟧TheoryTy ⟦_⟧⊗
      ⊢ Trace (Sum.inl (N .src t))
    tail-step t z =
      z ∘⊢ ⊗-map id⊢ P' ∘⊢ ⊗-assoc⁻ ∘⊢ step-out (Sum.inl t) Eq.refl

    stepN'-comp : (t : ⟨ N' .transition ⟩)
      → (⟦ A'.branch (N' .src t) (A'.step t Eq.refl) ⟧TheoryTy A'.Trace
        ⊢ ⟦ A'.branch (N' .src t) (A'.step t Eq.refl) ⟧TheoryTy ⟦_⟧N')
      → ⟦ branch (Sum.inr (N' .src t)) (step (Sum.inr t) Eq.refl) ⟧TheoryTy ⟦_⟧⊗
        ⊢ Trace (Sum.inr (N' .src t))
    stepN'-comp t z =
      STEP (Sum.inr t) ∘⊢ A'.step-out t Eq.refl ∘⊢ z ∘⊢ A'.step-in t Eq.refl
        ∘⊢ ⊗-map id⊢ lowerTy ∘⊢ step-out (Sum.inr t) Eq.refl

    roll-step : ∀ (t : ⟨ ⊗Trans ⟩)
      → (⟦ branch (⊗NFA .src t) (step t Eq.refl) ⟧TheoryTy ⟦_⟧⊗
        ⊢ ⟦ branch (⊗NFA .src t) (step t Eq.refl) ⟧TheoryTy Trace)
      → ⟦ branch (⊗NFA .src t) (step t Eq.refl) ⟧TheoryTy ⟦_⟧⊗
        ⊢ Trace (⊗NFA .src t)
    roll-step t z = roll ∘⊢ σ⊕ (step t Eq.refl) ∘⊢ z

  gmap-homo : ∀ q → gmap q ∘⊢ ⊗Alg q ≡ roll ∘⊢ map (TraceTy q) gmap
  gmap-homo (Sum.inl q) = ⊕ᴰ≡ _ _ λ where
    (stop ())
    (step (Sum.inl t) Eq.refl) →
      cong (lhs-step t) (A.map-step N→⟜ t Eq.refl)
      ∙ cong (tail-step t) (⟜-β (W-step t))
      ∙ cong (mid-step t) (⊗-assoc∘⊗-assoc⁻ {A = literal (N .label t)}
                             {B = A.Trace (N .dst t)} {C = A'.Parse})
      ∙ cong (roll-step (Sum.inl t)) (sym (map-step gmap (Sum.inl t) Eq.refl))
    (step (Sum.inr t) ())
    (stepε (N-acc _ acc) Eq.refl) →
      cong (tail-acc q acc) (⟜-β (W-acc q acc))
      ∙ cong (accL q acc) (sym (⊗-unit-l-nat↑ P'))
      ∙ cong (accR q acc) (⊗-unit-l∘l⁻ {A = A'.Parse})
    (stepε (N-ε-trans t) Eq.refl) → cong (tail-ε t) (⟜-β (W-ε t))
    (stepε (N'-ε-trans t) ())
  gmap-homo (Sum.inr q') = ⊕ᴰ≡ _ _ λ where
    (stop acc) → refl
    (step (Sum.inl t) ())
    (step (Sum.inr t) Eq.refl) →
      cong (stepN'-comp t) (A'.map-step N'→⊗NFA t Eq.refl)
      ∙ cong (roll-step (Sum.inr t)) (sym (map-step gmap (Sum.inr t) Eq.refl))
    (stepε (N-acc _ _) ())
    (stepε (N-ε-trans t) ())
    (stepε (N'-ε-trans t) Eq.refl) → refl

  ⊗NFA-ret : ∀ q → N→⊗NFA q ∘⊢ fromNFA (Sum.inl q) ≡ id⊢
  ⊗NFA-ret q = rec-section TraceTy ⊗Alg gmap gmap-homo (Sum.inl q)

  -- The `N'` half of the section: `fromNFA` read as a map out of `N'`'s own
  -- traces is a retraction of `N'→⊗NFA`.
  fromN' : ∀ q' → ⟦ q' ⟧N' ⊢ A'.Trace q'
  fromN' q' = lowerTy ∘⊢ fromNFA (Sum.inr q')

  private
    stepN'-comp⁻ : (t : ⟨ N' .transition ⟩)
      → (⟦ branch (Sum.inr (N' .src t)) (step (Sum.inr t) Eq.refl) ⟧TheoryTy Trace
        ⊢ ⟦ branch (Sum.inr (N' .src t)) (step (Sum.inr t) Eq.refl) ⟧TheoryTy ⟦_⟧⊗)
      → ⟦ A'.branch (N' .src t) (A'.step t Eq.refl) ⟧TheoryTy ⟦_⟧N'
        ⊢ A'.Trace (N' .src t)
    stepN'-comp⁻ t z =
      A'.STEP t ∘⊢ ⊗-map id⊢ lowerTy ∘⊢ step-out (Sum.inr t) Eq.refl ∘⊢ z
        ∘⊢ step-in (Sum.inr t) Eq.refl ∘⊢ A'.step-out t Eq.refl

    rollN'-step : (t : ⟨ N' .transition ⟩)
      → (⟦ A'.branch (N' .src t) (A'.step t Eq.refl) ⟧TheoryTy ⟦_⟧N'
        ⊢ ⟦ A'.branch (N' .src t) (A'.step t Eq.refl) ⟧TheoryTy A'.Trace)
      → ⟦ A'.branch (N' .src t) (A'.step t Eq.refl) ⟧TheoryTy ⟦_⟧N'
        ⊢ A'.Trace (N' .src t)
    rollN'-step t z = roll ∘⊢ σ⊕ (A'.step t Eq.refl) ∘⊢ z

  fromN'-homo : ∀ q' → fromN' q' ∘⊢ N'Alg q'
                     ≡ roll ∘⊢ map (A'.TraceTy q') fromN'
  fromN'-homo q' = ⊕ᴰ≡ _ _ λ where
    (A'.stop acc) → refl
    (A'.step t Eq.refl) →
      cong (stepN'-comp⁻ t) (map-step fromNFA (Sum.inr t) Eq.refl)
      ∙ cong (rollN'-step t) (sym (A'.map-step fromN' t Eq.refl))
    (A'.stepε t Eq.refl) → refl

  fromN'-section : ∀ q' → fromN' q' ∘⊢ N'→⊗NFA q' ≡ id⊢
  fromN'-section = rec-section A'.TraceTy N'Alg fromN' fromN'-homo

  -- The section.  `fromNFA ∘ N→⊗NFA` is compared with the identity in
  -- *curried* form: the `N'` parse that the crossing spends is abstracted
  -- with `⟜`, so the induction runs on `N`'s trace alone.  `⟜-η` is `refl`,
  -- so `cong ⟜-intro` moves each branch back to an equation between
  -- uncurried maps with no bookkeeping.
  private
    C⟜ : ⟨ N .Q ⟩ → TheoryTy ℓ⊗ tt
    C⟜ q = (A.Trace q ⊗ A'.Parse) ⟜ A'.Parse

    -- `fromNFA` is applied *outside* the residual, so that uncurrying a
    -- branch leaves it outside too.  `⟜-post-intro⁻` is what says so.
    secL secR : ∀ q → A.Trace q ⊢ C⟜ q
    secL q = ⟜-post (fromNFA (Sum.inl q)) ∘⊢ ⟜-precomp P' ∘⊢ N→⟜ q
    secR q = ⟜-intro id⊢

    Eqr : ⟨ N .Q ⟩ → TheoryTy ℓ⊗ tt
    Eqr x = equalizer (secL x) (secR x)

    eqπ : ∀ x → Eqr x ⊢ A.Trace x
    eqπ x = eq-π (secL x) (secR x)

    F' : Trace (Sum.inr (N' .init)) ⊢ A'.Parse
    F' = fromN' (N' .init)

    roll-branch : ∀ q (tg : A.Tag q) → ⟦ A.branch q tg ⟧TheoryTy Eqr ⊢ A.Trace q
    roll-branch q tg = roll ∘⊢ map (A.TraceTy q) eqπ ∘⊢ σ⊕ tg

    -- Both sides of the induction, uncurried once.  `⟜-β` is the only
    -- non-definitional step.
    secL-uncurry : ∀ {ℓD} {D : TheoryTy ℓD tt} q (h : D ⊢ A.Trace q)
      → ⟜-intro⁻ (secL q ∘⊢ h)
        ≡ fromNFA (Sum.inl q) ∘⊢ ⟜-intro⁻ (N→⟜ q ∘⊢ h) ∘⊢ ⊗-map id⊢ P'
    secL-uncurry q h =
      ⟜-post-precomp-intro⁻ (fromNFA (Sum.inl q)) P' (N→⟜ q ∘⊢ h)

    secR-uncurry : ∀ {ℓD} {D : TheoryTy ℓD tt} q (h : D ⊢ A.Trace q)
      → ⟜-intro⁻ (secR q ∘⊢ h) ≡ ⊗-map h id⊢
    secR-uncurry q h = ⟜-β _

    V-acc : ∀ q (acc : true Eq.≡ N .isAcc q)
      → ⟦ A.branch q (A.stop acc) ⟧TheoryTy Eqr ⊗ Trace (Sum.inr (N' .init))
      ⊢ Trace (Sum.inl q)
    V-acc q acc = STEPε (N-acc q acc) ∘⊢ ⊗-unit-l
      ∘⊢ ⊗-map (lowerTy ∘⊢ lowerTy) id⊢

    V-ε : (t : ⟨ N .ε-transition ⟩)
      → ⟦ A.branch (N .ε-src t) (A.stepε t Eq.refl) ⟧TheoryTy Eqr
        ⊗ Trace (Sum.inr (N' .init))
      ⊢ Trace (Sum.inl (N .ε-src t))
    V-ε t = STEPε (N-ε-trans t) ∘⊢ ⟜-app
      ∘⊢ ⊗-map (N→⟜ (N .ε-dst t) ∘⊢ eqπ (N .ε-dst t) ∘⊢ lowerTy) id⊢

    V-step : (t : ⟨ N .transition ⟩)
      → ⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy Eqr
        ⊗ Trace (Sum.inr (N' .init))
      ⊢ Trace (Sum.inl (N .src t))
    V-step t = STEP (Sum.inl t) ∘⊢ ⊗-map id⊢ ⟜-app ∘⊢ ⊗-assoc
      ∘⊢ ⊗-map (A.step-out t Eq.refl) id⊢
      ∘⊢ ⊗-map (map (A.branch (N .src t) (A.step t Eq.refl))
                    (λ x → N→⟜ x ∘⊢ eqπ x)) id⊢

    accA : ∀ {ℓD} {D : TheoryTy ℓD tt} q
      → (D ⊗ Trace (Sum.inr (N' .init)) ⊢ Trace (Sum.inl q))
      → D ⊗ A'.Parse ⊢ A.Trace q ⊗ A'.Parse
    accA q z = fromNFA (Sum.inl q) ∘⊢ z ∘⊢ ⊗-map id⊢ P'

    accB : ∀ {ℓD} {D : TheoryTy ℓD tt} q (acc : true Eq.≡ N .isAcc q)
      → (εTy ⊗ Trace (Sum.inr (N' .init)) ⊢ A'.Parse) → (D ⊢ εTy)
      → D ⊗ A'.Parse ⊢ A.Trace q ⊗ A'.Parse
    accB q acc z d = ⊗-map (A.STOP acc) id⊢ ∘⊢ ⊗ε-unit-l⁻ ∘⊢ z ∘⊢ ⊗-map d P'

    accB2 : ∀ {ℓD} {D : TheoryTy ℓD tt} q (acc : true Eq.≡ N .isAcc q)
      → (εTy ⊗ A'.Parse ⊢ εTy ⊗ A'.Parse) → (D ⊢ εTy)
      → D ⊗ A'.Parse ⊢ A.Trace q ⊗ A'.Parse
    accB2 q acc z d = ⊗-map (A.STOP acc) id⊢ ∘⊢ z ∘⊢ ⊗-map id⊢ F' ∘⊢ ⊗-map d P'

    accC : ∀ {ℓD} {D : TheoryTy ℓD tt} q (acc : true Eq.≡ N .isAcc q)
      → (A'.Parse ⊢ A'.Parse) → (D ⊢ εTy)
      → D ⊗ A'.Parse ⊢ A.Trace q ⊗ A'.Parse
    accC q acc z d = ⊗-map (A.STOP acc) id⊢ ∘⊢ ⊗-map d z

    stepA : (t : ⟨ N .transition ⟩)
      → (⟦ branch (Sum.inl (N .src t)) (step (Sum.inl t) Eq.refl) ⟧TheoryTy Trace
        ⊢ ⟦ branch (Sum.inl (N .src t)) (step (Sum.inl t) Eq.refl) ⟧TheoryTy ⟦_⟧⊗)
      → ⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy Eqr ⊗ A'.Parse
        ⊢ A.Trace (N .src t) ⊗ A'.Parse
    stepA t z = ⊗-map (A.STEP t) id⊢ ∘⊢ ⊗-assoc⁻ ∘⊢ step-out (Sum.inl t) Eq.refl
      ∘⊢ z ∘⊢ step-in (Sum.inl t) Eq.refl
      ∘⊢ ⊗-map id⊢ ⟜-app ∘⊢ ⊗-assoc ∘⊢ ⊗-map (A.step-out t Eq.refl) id⊢
      ∘⊢ ⊗-map (map (A.branch (N .src t) (A.step t Eq.refl))
                    (λ x → N→⟜ x ∘⊢ eqπ x)) id⊢
      ∘⊢ ⊗-map id⊢ P'

    stepB : (t : ⟨ N .transition ⟩)
      → (⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy Eqr
        ⊢ ⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy ⟦_⟧N)
      → ⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy Eqr ⊗ A'.Parse
        ⊢ A.Trace (N .src t) ⊗ A'.Parse
    stepB t z = ⊗-map (A.STEP t) id⊢ ∘⊢ ⊗-assoc⁻
      ∘⊢ ⊗-map id⊢ (fromNFA (Sum.inl (N .dst t)) ∘⊢ ⟜-app)
      ∘⊢ ⊗-assoc ∘⊢ ⊗-map (A.step-out t Eq.refl ∘⊢ z) P'

    stepC : (t : ⟨ N .transition ⟩)
      → (Eqr (N .dst t) ⊗ A'.Parse ⊢ A.Trace (N .dst t) ⊗ A'.Parse)
      → ⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy Eqr ⊗ A'.Parse
        ⊢ A.Trace (N .src t) ⊗ A'.Parse
    stepC t z = ⊗-map (A.STEP t) id⊢ ∘⊢ ⊗-assoc⁻ ∘⊢ ⊗-map id⊢ z ∘⊢ ⊗-assoc
      ∘⊢ ⊗-map (A.step-out t Eq.refl) id⊢

    stepD : (t : ⟨ N .transition ⟩)
      → ((literal (N .label t) ⊗ Eqr (N .dst t)) ⊗ A'.Parse
        ⊢ (literal (N .label t) ⊗ Eqr (N .dst t)) ⊗ A'.Parse)
      → ⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy Eqr ⊗ A'.Parse
        ⊢ A.Trace (N .src t) ⊗ A'.Parse
    stepD t z = ⊗-map (A.STEP t) id⊢
      ∘⊢ ⊗-map (⊗-map id⊢ (eqπ (N .dst t))) id⊢
      ∘⊢ z ∘⊢ ⊗-map (A.step-out t Eq.refl) id⊢

    stepE : (t : ⟨ N .transition ⟩)
      → (⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy Eqr
        ⊢ ⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy A.Trace)
      → ⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy Eqr ⊗ A'.Parse
        ⊢ A.Trace (N .src t) ⊗ A'.Parse
    stepE t z = ⊗-map (roll ∘⊢ σ⊕ (A.step t Eq.refl) ∘⊢ z) id⊢

    εA : ∀ {ℓD} {D : TheoryTy ℓD tt} (t : ⟨ N .ε-transition ⟩)
      → (D ⊗ A'.Parse ⊢ A.Trace (N .ε-dst t) ⊗ A'.Parse)
      → D ⊗ A'.Parse ⊢ A.Trace (N .ε-src t) ⊗ A'.Parse
    εA t z = ⊗-map (A.STEPε t) id⊢ ∘⊢ z

  ⊗NFA-sec : ∀ q → fromNFA (Sum.inl q) ∘⊢ N→⊗NFA q ≡ id⊢
  ⊗NFA-sec q =
    sym (secL-uncurry q id⊢)
    ∙ cong ⟜-intro⁻ (equalizer-ind A.TraceTy C⟜ secL secR branch-eq q)
    ∙ secR-uncurry q id⊢
    where
    branch-eq : ∀ q → secL q ∘⊢ roll ∘⊢ map (A.TraceTy q) eqπ
             ≡ secR q ∘⊢ roll ∘⊢ map (A.TraceTy q) eqπ
    branch-eq q = ⊕ᴰ≡ _ _ λ where
      (A.stop acc) → cong ⟜-intro
        ( secL-uncurry q (roll-branch q (A.stop acc))
        ∙ cong (accA q) (⟜-β (V-acc q acc))
        ∙ cong (λ z → accB q acc z (lowerTy ∘⊢ lowerTy)) (⊗-unit-l-nat↑ F')
        ∙ cong (λ z → accB2 q acc z (lowerTy ∘⊢ lowerTy))
               (⊗-unit-l⁻∘l {A = A'.Parse})
        ∙ cong (λ z → accC q acc z (lowerTy ∘⊢ lowerTy))
               (fromN'-section (N' .init))
        ∙ sym (secR-uncurry q (roll-branch q (A.stop acc))) )
      (A.step t Eq.refl) → cong ⟜-intro
        ( secL-uncurry (N .src t) (roll-branch (N .src t) (A.step t Eq.refl))
        ∙ cong (accA (N .src t)) (⟜-β (V-step t))
        ∙ cong (stepA t) (map-step fromNFA (Sum.inl t) Eq.refl)
        ∙ cong (stepB t) (A.map-step (λ x → N→⟜ x ∘⊢ eqπ x) t Eq.refl)
        ∙ cong (stepC t) (sym (secL-uncurry (N .dst t) (eqπ (N .dst t))))
        ∙ cong (stepC t)
               (cong ⟜-intro⁻ (eq-π-pf (secL (N .dst t)) (secR (N .dst t))))
        ∙ cong (stepC t) (secR-uncurry (N .dst t) (eqπ (N .dst t)))
        ∙ cong (stepD t) (⊗-assoc⁻∘⊗-assoc {A = literal (N .label t)}
                            {B = Eqr (N .dst t)} {C = A'.Parse})
        ∙ cong (stepE t) (sym (A.map-step eqπ t Eq.refl))
        ∙ sym (secR-uncurry (N .src t)
                 (roll-branch (N .src t) (A.step t Eq.refl))) )
      (A.stepε t Eq.refl) → cong ⟜-intro
        ( secL-uncurry (N .ε-src t)
            (roll-branch (N .ε-src t) (A.stepε t Eq.refl))
        ∙ cong (accA (N .ε-src t)) (⟜-β (V-ε t))
        ∙ cong (εA t) (sym (secL-uncurry (N .ε-dst t)
                              (eqπ (N .ε-dst t) ∘⊢ lowerTy)))
        ∙ cong (εA t) (cong ⟜-intro⁻
            (cong (_∘⊢ lowerTy)
                  (eq-π-pf (secL (N .ε-dst t)) (secR (N .ε-dst t)))))
        ∙ cong (εA t) (secR-uncurry (N .ε-dst t) (eqπ (N .ε-dst t) ∘⊢ lowerTy))
        ∙ sym (secR-uncurry (N .ε-src t)
                 (roll-branch (N .ε-src t) (A.stepε t Eq.refl))) )

  ⊗NFA≅ : Parse ≅ (A.Parse ⊗ A'.Parse)
  ⊗NFA≅ .fun = fromNFA (Sum.inl (N .init))
  ⊗NFA≅ .inv = N→⊗NFA (N .init)
  ⊗NFA≅ .sec = ⊗NFA-sec (N .init)
  ⊗NFA≅ .ret = ⊗NFA-ret (N .init)
