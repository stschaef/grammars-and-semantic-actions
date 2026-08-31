{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Thompson's construction at `*`: a fresh accepting state with a silent
   transition into `N`'s start, and one back out of each of `N`'s accepting
   states.

   Two folds meet here.  `from*NFA` folds the automaton's trace into a list
   of `N` parses; `to*NFA` folds *that list* back, and inside it a second
   fold turns each `N` trace into a `*NFA` trace still owing the rest of the
   list.  The bridge between them is `nested-induction`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.WildCat.LocallySmall.Base
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Thompson.Construction.KleeneStar
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Relation.Nullary.Base using (Dec)
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Relation.Nullary.DecidablePropositions.More
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.Properties using (isFinSetUnit ; isFinSetBool
                                                 ; EquivPresIsFinSet)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Sum as Sum
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Convolution Alphabet isSetAlphabet
  using (⊗e-ε→ ; ⊗e-ε← ; ⊗e-ε-map ; ⟦⊗e⟧ ; ⟦⊗e⟧⁻ ; ⟦⊗e⟧-η ; ⟦⊗e⟧-β
        ; ⟦⊗e⟧-nat ; ⟦⊗e⟧⁻-nat)
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (_⟜_ ; ⟜-intro ; ⟜-intro⁻ ; ⟜-app ; ⟜-β ; ⟜-post ; ⟜-precomp
        ; ⊗ε-unit-l⁻)
open import Theory.Instances.Monoid.Residual.Laws Alphabet isSetAlphabet
  using (⟜-post-precomp-intro⁻ ; ⟜-post-intro⁻)
open import Theory.Instances.Monoid.Unitor Alphabet isSetAlphabet
  using (⊗-assoc⁻∘⊗-assoc ; ⊗-assoc∘⊗-assoc⁻ ; ⊗-unit-l∘l⁻ ; ⊗-unit-l⁻∘l
        ; ⊗-unit-l-nat↑)
open import Theory.Instances.Monoid.Automata.NFA.Base Alphabet isSetAlphabet

open WildCatNotation
open WildCatIso
open Iso
open NFA

private variable ℓN : Level

module _ (N : NFA ℓN) where
  private
    module A = NFA.Accepting N

  data *εTrans : Type ℓN where
    inr' : *εTrans
    cons⟨N⟩ : ∀ {q} → true Eq.≡ N .isAcc q → *εTrans
    N-internal : ⟨ N .ε-transition ⟩ → *εTrans

  *εTrans-rep :
    (Unit Sum.⊎ ((Σ[ q ∈ ⟨ N .Q ⟩ ] (true Eq.≡ N .isAcc q))
      Sum.⊎ ⟨ N .ε-transition ⟩))
    ≃ *εTrans
  *εTrans-rep = isoToEquiv (iso to from tf ft)
    where
    Src = Unit Sum.⊎ ((Σ[ q ∈ ⟨ N .Q ⟩ ] (true Eq.≡ N .isAcc q))
      Sum.⊎ ⟨ N .ε-transition ⟩)

    to : Src → *εTrans
    to (Sum.inl _) = inr'
    to (Sum.inr (Sum.inl x)) = cons⟨N⟩ (x .snd)
    to (Sum.inr (Sum.inr x)) = N-internal x

    from : *εTrans → Src
    from inr' = Sum.inl tt
    from (cons⟨N⟩ {q} x) = Sum.inr (Sum.inl (q , x))
    from (N-internal x) = Sum.inr (Sum.inr x)

    tf : ∀ y → to (from y) ≡ y
    tf inr' = refl
    tf (cons⟨N⟩ x) = refl
    tf (N-internal x) = refl

    ft : ∀ y → from (to y) ≡ y
    ft (Sum.inl _) = refl
    ft (Sum.inr (Sum.inl x)) = refl
    ft (Sum.inr (Sum.inr x)) = refl

  *NFA : NFA ℓN
  *NFA .Q = Unit Sum.⊎ ⟨ N .Q ⟩ , isFinSet⊎ (_ , isFinSetUnit) (N .Q)
  *NFA .init = Sum.inl tt
  *NFA .isAcc (Sum.inl _) = true
  *NFA .isAcc (Sum.inr q) = false
  *NFA .transition = N .transition
  *NFA .src = Sum.inr ∘ N .src
  *NFA .dst = Sum.inr ∘ N .dst
  *NFA .label = N .label
  *NFA .ε-transition = *εTrans , EquivPresIsFinSet *εTrans-rep
    (isFinSet⊎ (_ , isFinSetUnit)
      (_ , isFinSet⊎
        (_ , isFinSetΣ (N .Q) λ q →
          _ , isDecProp→isFinSet (the-dec-prop q .fst .snd) (the-dec-prop q .snd))
        (N .ε-transition)))
    where
    the-dec-prop : ⟨ N .Q ⟩ → Σ (hProp ℓ-zero) λ P → Dec (P .fst)
    the-dec-prop q = isFinSet→DecProp-Eq≡ isFinSetBool true (N .isAcc q)
  *NFA .ε-src inr' = Sum.inl tt
  *NFA .ε-dst inr' = Sum.inr (N .init)
  *NFA .ε-src (cons⟨N⟩ {q} _) = Sum.inr q
  *NFA .ε-dst (cons⟨N⟩ _) = Sum.inl tt
  *NFA .ε-src (N-internal t) = Sum.inr (N .ε-src t)
  *NFA .ε-dst (N-internal t) = Sum.inr (N .ε-dst t)

  open NFA.Accepting *NFA

  ℓ* : Level
  ℓ* = ℓF (ℓ-max (ℓF (ℓ⋆ ℓN)) ℓN)

  -- What is owed from a state: at the fresh state the rest of the list, at
  -- one of `N`'s the rest of that parse *and* the rest of the list.
  ⟦_⟧* : Unit Sum.⊎ ⟨ N .Q ⟩ → TheoryTy ℓ* tt
  ⟦ Sum.inl _ ⟧* = A.Parse *
  ⟦ Sum.inr q ⟧* = A.Trace q ⊗ (A.Parse *)

  *NFAAlg : TraceAlg ⟦_⟧*
  -- `NIL`/`CONS` are spelled out through `⟦⊗e⟧` rather than used directly:
  -- the star's own constructors bundle a `two`, and every law below would
  -- then have to unbundle it again.
  *NFAAlg (Sum.inl _) = ⊕ᴰ-elim λ where
    (stop Eq.refl) → roll ∘⊢ σ⊕ false ∘⊢ ⊗e-ε← _ ∘⊢ lowerTy ∘⊢ lowerTy
    (stepε inr' Eq.refl) →
      roll ∘⊢ σ⊕ true ∘⊢ ⟦⊗e⟧⁻ _ _ ∘⊢ ⊗-map liftTy liftTy ∘⊢ lowerTy
    (stepε (cons⟨N⟩ acc) ())
    (stepε (N-internal t) ())
  *NFAAlg (Sum.inr q) = ⊕ᴰ-elim λ where
    (stop ())
    (step t Eq.refl) →
      ⊗-map (A.STEP t) id⊢ ∘⊢ ⊗-assoc⁻ ∘⊢ step-out t Eq.refl
    (stepε inr' ())
    (stepε (cons⟨N⟩ acc) Eq.refl) →
      ⊗-map (A.STOP acc) id⊢ ∘⊢ ⊗ε-unit-l⁻ ∘⊢ lowerTy
    (stepε (N-internal t) Eq.refl) → ⊗-map (A.STEPε t) id⊢ ∘⊢ lowerTy

  from*NFA : ∀ q → Trace q ⊢ ⟦ q ⟧*
  from*NFA = rec TraceTy *NFAAlg

  -- `N`'s trace as a `*NFA` trace still owing the rest of the list
  ⟦_⟧N : ⟨ N .Q ⟩ → TheoryTy (ℓ-max (ℓF (ℓ⋆ ℓN)) ℓN) tt
  ⟦ q ⟧N = Trace (Sum.inr q) ⟜ Trace (Sum.inl tt)

  NAlg : A.TraceAlg ⟦_⟧N
  NAlg q = ⊕ᴰ-elim λ where
    (A.stop acc) →
      ⟜-intro (STEPε (cons⟨N⟩ acc) ∘⊢ ⊗-unit-l
                ∘⊢ ⊗-map (lowerTy ∘⊢ lowerTy) id⊢)
    (A.step t Eq.refl) →
      ⟜-intro (STEP t ∘⊢ ⊗-map id⊢ ⟜-app ∘⊢ ⊗-assoc
                ∘⊢ ⊗-map (A.step-out t Eq.refl) id⊢)
    (A.stepε t Eq.refl) →
      ⟜-intro (STEPε (N-internal t) ∘⊢ ⟜-app ∘⊢ ⊗-map lowerTy id⊢)

  N→⟜ : ∀ q → A.Trace q ⊢ ⟦ q ⟧N
  N→⟜ = rec A.TraceTy NAlg

  -- ...and the list of them, folded back into one trace
  N*Alg : ∀ (_ : Unit) → ⟦ StarCode A.Parse ⟧TheoryTy (λ _ → Trace (Sum.inl tt))
                       ⊢ Trace (Sum.inl tt)
  N*Alg _ = ⊕ᴰ-elim λ where
    false → STOP Eq.refl ∘⊢ ⊗e-ε→ _
    true → STEPε inr' ∘⊢ ⟜-app ∘⊢ ⊗-map (N→⟜ (N .init)) id⊢
             ∘⊢ ⊗-map lowerTy lowerTy ∘⊢ ⟦⊗e⟧ _ _

  to*NFA : ∀ q → ⟦ q ⟧* ⊢ Trace q
  to*NFA (Sum.inl _) = rec (λ _ → StarCode A.Parse) N*Alg tt
  to*NFA (Sum.inr q) =
    ⟜-intro⁻ (N→⟜ q) ∘⊢ ⊗-map id⊢ (to*NFA (Sum.inl tt))

  private
    T* : A.Parse * ⊢ Trace (Sum.inl tt)
    T* = to*NFA (Sum.inl tt)

    -- the shapes `ret`'s branches pass through
    starA : ∀ {ℓD} {D : TheoryTy ℓD tt}
      → (D ⊢ ⟦ starBranch A.Parse true ⟧TheoryTy (λ _ → Trace (Sum.inl tt)))
      → (⟦ branch (Sum.inl tt) (stepε inr' Eq.refl) ⟧TheoryTy ⟦_⟧* ⊢ D)
      → ⟦ branch (Sum.inl tt) (stepε inr' Eq.refl) ⟧TheoryTy ⟦_⟧*
        ⊢ Trace (Sum.inl tt)
    starA z d = N*Alg tt ∘⊢ σ⊕ true ∘⊢ z ∘⊢ d

    stepA : (t : ⟨ N .transition ⟩)
      → (literal (N .label t) ⊗ (A.Trace (N .dst t) ⊗ (A.Parse *))
        ⊢ literal (N .label t) ⊗ (A.Trace (N .dst t) ⊗ (A.Parse *)))
      → ⟦ branch (Sum.inr (N .src t)) (step t Eq.refl) ⟧TheoryTy ⟦_⟧*
        ⊢ Trace (Sum.inr (N .src t))
    stepA t z = STEP t ∘⊢ ⊗-map id⊢ (to*NFA (Sum.inr (N .dst t))) ∘⊢ z
      ∘⊢ step-out t Eq.refl

    W-step : (t : ⟨ N .transition ⟩)
      → (literal (N .label t) ⊗ A.Trace (N .dst t)) ⊗ Trace (Sum.inl tt)
      ⊢ Trace (Sum.inr (N .src t))
    W-step t = STEP t ∘⊢ ⊗-map id⊢ ⟜-app ∘⊢ ⊗-assoc
      ∘⊢ ⊗-map (⊗-map id⊢ (N→⟜ (N .dst t))) id⊢

    tail-step : (t : ⟨ N .transition ⟩)
      → ((literal (N .label t) ⊗ A.Trace (N .dst t)) ⊗ Trace (Sum.inl tt)
        ⊢ Trace (Sum.inr (N .src t)))
      → ⟦ branch (Sum.inr (N .src t)) (step t Eq.refl) ⟧TheoryTy ⟦_⟧*
        ⊢ Trace (Sum.inr (N .src t))
    tail-step t z = z ∘⊢ ⊗-map id⊢ T* ∘⊢ ⊗-assoc⁻ ∘⊢ step-out t Eq.refl

    lhs-step : (t : ⟨ N .transition ⟩)
      → (⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy A.Trace
        ⊢ ⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy ⟦_⟧N)
      → ⟦ branch (Sum.inr (N .src t)) (step t Eq.refl) ⟧TheoryTy ⟦_⟧*
        ⊢ Trace (Sum.inr (N .src t))
    lhs-step t z =
      ⟜-intro⁻ (NAlg-step t ∘⊢ z ∘⊢ A.step-in t Eq.refl)
        ∘⊢ ⊗-map id⊢ T* ∘⊢ ⊗-assoc⁻ ∘⊢ step-out t Eq.refl
      where
      NAlg-step : (t' : ⟨ N .transition ⟩)
        → ⟦ A.branch (N .src t') (A.step t' Eq.refl) ⟧TheoryTy ⟦_⟧N
        ⊢ ⟦ N .src t' ⟧N
      NAlg-step t' = ⟜-intro (STEP t' ∘⊢ ⊗-map id⊢ ⟜-app ∘⊢ ⊗-assoc
        ∘⊢ ⊗-map (A.step-out t' Eq.refl) id⊢)

    W-acc : ∀ q (acc : true Eq.≡ N .isAcc q)
      → εTy ⊗ Trace (Sum.inl tt) ⊢ Trace (Sum.inr q)
    W-acc q acc = STEPε (cons⟨N⟩ acc) ∘⊢ ⊗-unit-l

    tail-acc : ∀ q (acc : true Eq.≡ N .isAcc q)
      → (εTy ⊗ Trace (Sum.inl tt) ⊢ Trace (Sum.inr q))
      → ⟦ branch (Sum.inr q) (stepε (cons⟨N⟩ acc) Eq.refl) ⟧TheoryTy ⟦_⟧*
      ⊢ Trace (Sum.inr q)
    tail-acc q acc z = z ∘⊢ ⊗-map id⊢ T* ∘⊢ ⊗ε-unit-l⁻ ∘⊢ lowerTy

    accL : ∀ q (acc : true Eq.≡ N .isAcc q)
      → (εTy ⊗ (A.Parse *) ⊢ Trace (Sum.inl tt))
      → ⟦ branch (Sum.inr q) (stepε (cons⟨N⟩ acc) Eq.refl) ⟧TheoryTy ⟦_⟧*
      ⊢ Trace (Sum.inr q)
    accL q acc z = STEPε (cons⟨N⟩ acc) ∘⊢ z ∘⊢ ⊗ε-unit-l⁻ ∘⊢ lowerTy

    accR : ∀ q (acc : true Eq.≡ N .isAcc q)
      → (A.Parse * ⊢ A.Parse *)
      → ⟦ branch (Sum.inr q) (stepε (cons⟨N⟩ acc) Eq.refl) ⟧TheoryTy ⟦_⟧*
      ⊢ Trace (Sum.inr q)
    accR q acc z = STEPε (cons⟨N⟩ acc) ∘⊢ T* ∘⊢ z ∘⊢ lowerTy

    W-ε : (t : ⟨ N .ε-transition ⟩)
      → A.Trace (N .ε-dst t) ⊗ Trace (Sum.inl tt)
      ⊢ Trace (Sum.inr (N .ε-src t))
    W-ε t = STEPε (N-internal t) ∘⊢ ⟜-app ∘⊢ ⊗-map (N→⟜ (N .ε-dst t)) id⊢

    tail-ε : (t : ⟨ N .ε-transition ⟩)
      → (A.Trace (N .ε-dst t) ⊗ Trace (Sum.inl tt)
        ⊢ Trace (Sum.inr (N .ε-src t)))
      → ⟦ branch (Sum.inr (N .ε-src t)) (stepε (N-internal t) Eq.refl) ⟧TheoryTy ⟦_⟧*
      ⊢ Trace (Sum.inr (N .ε-src t))
    tail-ε t z = z ∘⊢ ⊗-map id⊢ T* ∘⊢ lowerTy

    roll-step : (t : ⟨ N .transition ⟩)
      → (⟦ branch (Sum.inr (N .src t)) (step t Eq.refl) ⟧TheoryTy ⟦_⟧*
        ⊢ ⟦ branch (Sum.inr (N .src t)) (step t Eq.refl) ⟧TheoryTy Trace)
      → ⟦ branch (Sum.inr (N .src t)) (step t Eq.refl) ⟧TheoryTy ⟦_⟧*
        ⊢ Trace (Sum.inr (N .src t))
    roll-step t z = roll ∘⊢ σ⊕ (step t Eq.refl) ∘⊢ z

  to*NFA-homo : ∀ q → to*NFA q ∘⊢ *NFAAlg q ≡ roll ∘⊢ map (TraceTy q) to*NFA
  to*NFA-homo (Sum.inl _) = ⊕ᴰ≡ _ _ λ where
    (stop Eq.refl) → refl
    (stepε inr' Eq.refl) →
      cong (λ z → starA z (⊗-map liftTy liftTy ∘⊢ lowerTy))
           (⟦⊗e⟧⁻-nat (k A.Parse) (Var tt) (λ _ → T*))
    (stepε (cons⟨N⟩ acc) ())
    (stepε (N-internal t) ())
  to*NFA-homo (Sum.inr q) = ⊕ᴰ≡ _ _ λ where
    (stop ())
    (step t Eq.refl) →
      cong (lhs-step t) (A.map-step N→⟜ t Eq.refl)
      ∙ cong (tail-step t) (⟜-β (W-step t))
      ∙ cong (stepA t) (⊗-assoc∘⊗-assoc⁻ {A = literal (N .label t)}
                          {B = A.Trace (N .dst t)} {C = A.Parse *})
      ∙ cong (roll-step t) (sym (map-step to*NFA t Eq.refl))
    (stepε inr' ())
    (stepε (cons⟨N⟩ acc) Eq.refl) →
      cong (tail-acc q acc) (⟜-β (W-acc q acc))
      ∙ cong (accL q acc) (sym (⊗-unit-l-nat↑ T*))
      ∙ cong (accR q acc) (⊗-unit-l∘l⁻ {A = A.Parse *})
    (stepε (N-internal t) Eq.refl) → cong (tail-ε t) (⟜-β (W-ε t))

  *NFA-ret : ∀ q → to*NFA q ∘⊢ from*NFA q ≡ id⊢
  *NFA-ret = rec-section TraceTy *NFAAlg to*NFA to*NFA-homo

  -- The bridge between the two folds: running `N`'s trace into the automaton
  -- and reading it back out again returns the trace and the rest of the list.
  -- Stated in curried form, so the induction is on `N`'s trace alone.
  private
    F* : Trace (Sum.inl tt) ⊢ A.Parse *
    F* = from*NFA (Sum.inl tt)

    C⟜ : ⟨ N .Q ⟩ → TheoryTy ℓ* tt
    C⟜ q = (A.Trace q ⊗ (A.Parse *)) ⟜ Trace (Sum.inl tt)

    nL nR : ∀ q → A.Trace q ⊢ C⟜ q
    nL q = ⟜-post (from*NFA (Sum.inr q)) ∘⊢ N→⟜ q
    nR q = ⟜-intro (⊗-map id⊢ F*)

    Eqr : ⟨ N .Q ⟩ → TheoryTy ℓ* tt
    Eqr x = equalizer (nL x) (nR x)

    eqπ : ∀ x → Eqr x ⊢ A.Trace x
    eqπ x = eq-π (nL x) (nR x)

    hOf : ∀ q (tg : A.Tag q) → ⟦ A.branch q tg ⟧TheoryTy Eqr ⊢ A.Trace q
    hOf q tg = roll ∘⊢ map (A.TraceTy q) eqπ ∘⊢ σ⊕ tg

    nL-uncurry : ∀ {ℓD} {D : TheoryTy ℓD tt} q (h : D ⊢ A.Trace q)
      → ⟜-intro⁻ (nL q ∘⊢ h)
        ≡ from*NFA (Sum.inr q) ∘⊢ ⟜-intro⁻ (N→⟜ q ∘⊢ h)
    nL-uncurry q h = ⟜-post-intro⁻ (from*NFA (Sum.inr q)) (N→⟜ q ∘⊢ h)

    nR-uncurry : ∀ {ℓD} {D : TheoryTy ℓD tt} q (h : D ⊢ A.Trace q)
      → ⟜-intro⁻ (nR q ∘⊢ h) ≡ ⊗-map h F*
    nR-uncurry q h = ⟜-β _

    -- `NAlg`'s three bodies at the equalizer carrier
    U-acc : ∀ q (acc : true Eq.≡ N .isAcc q)
      → ⟦ A.branch q (A.stop acc) ⟧TheoryTy Eqr ⊗ Trace (Sum.inl tt)
      ⊢ Trace (Sum.inr q)
    U-acc q acc = STEPε (cons⟨N⟩ acc) ∘⊢ ⊗-unit-l
      ∘⊢ ⊗-map (lowerTy ∘⊢ lowerTy) id⊢

    U-ε : (t : ⟨ N .ε-transition ⟩)
      → ⟦ A.branch (N .ε-src t) (A.stepε t Eq.refl) ⟧TheoryTy Eqr
        ⊗ Trace (Sum.inl tt)
      ⊢ Trace (Sum.inr (N .ε-src t))
    U-ε t = STEPε (N-internal t) ∘⊢ ⟜-app
      ∘⊢ ⊗-map (N→⟜ (N .ε-dst t) ∘⊢ eqπ (N .ε-dst t) ∘⊢ lowerTy) id⊢

    U-step : (t : ⟨ N .transition ⟩)
      → ⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy Eqr
        ⊗ Trace (Sum.inl tt)
      ⊢ Trace (Sum.inr (N .src t))
    U-step t = STEP t ∘⊢ ⊗-map id⊢ ⟜-app ∘⊢ ⊗-assoc
      ∘⊢ ⊗-map (A.step-out t Eq.refl) id⊢
      ∘⊢ ⊗-map (map (A.branch (N .src t) (A.step t Eq.refl))
                    (λ x → N→⟜ x ∘⊢ eqπ x)) id⊢

    -- the shapes each branch passes through
    nA : ∀ {ℓD} {D : TheoryTy ℓD tt} q
      → (D ⊗ Trace (Sum.inl tt) ⊢ Trace (Sum.inr q))
      → D ⊗ Trace (Sum.inl tt) ⊢ A.Trace q ⊗ (A.Parse *)
    nA q z = from*NFA (Sum.inr q) ∘⊢ z

    nB : ∀ {ℓD} {D : TheoryTy ℓD tt} q (acc : true Eq.≡ N .isAcc q)
      → (εTy ⊗ Trace (Sum.inl tt) ⊢ A.Parse *) → (D ⊢ εTy)
      → D ⊗ Trace (Sum.inl tt) ⊢ A.Trace q ⊗ (A.Parse *)
    nB q acc z d = ⊗-map (A.STOP acc) id⊢ ∘⊢ ⊗ε-unit-l⁻ ∘⊢ z ∘⊢ ⊗-map d id⊢

    nC : ∀ {ℓD} {D : TheoryTy ℓD tt} q (acc : true Eq.≡ N .isAcc q)
      → (εTy ⊗ (A.Parse *) ⊢ εTy ⊗ (A.Parse *)) → (D ⊢ εTy)
      → D ⊗ Trace (Sum.inl tt) ⊢ A.Trace q ⊗ (A.Parse *)
    nC q acc z d = ⊗-map (A.STOP acc) id⊢ ∘⊢ z ∘⊢ ⊗-map d F*

    εB : ∀ {ℓD} {D : TheoryTy ℓD tt} (t : ⟨ N .ε-transition ⟩)
      → (D ⊗ Trace (Sum.inl tt) ⊢ A.Trace (N .ε-dst t) ⊗ (A.Parse *))
      → D ⊗ Trace (Sum.inl tt) ⊢ A.Trace (N .ε-src t) ⊗ (A.Parse *)
    εB t z = ⊗-map (A.STEPε t) id⊢ ∘⊢ z

    sA : (t : ⟨ N .transition ⟩)
      → (⟦ branch (Sum.inr (N .src t)) (step t Eq.refl) ⟧TheoryTy Trace
        ⊢ ⟦ branch (Sum.inr (N .src t)) (step t Eq.refl) ⟧TheoryTy ⟦_⟧*)
      → ⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy Eqr
        ⊗ Trace (Sum.inl tt) ⊢ A.Trace (N .src t) ⊗ (A.Parse *)
    sA t z = ⊗-map (A.STEP t) id⊢ ∘⊢ ⊗-assoc⁻ ∘⊢ step-out t Eq.refl
      ∘⊢ z ∘⊢ step-in t Eq.refl
      ∘⊢ ⊗-map id⊢ ⟜-app ∘⊢ ⊗-assoc ∘⊢ ⊗-map (A.step-out t Eq.refl) id⊢
      ∘⊢ ⊗-map (map (A.branch (N .src t) (A.step t Eq.refl))
                    (λ x → N→⟜ x ∘⊢ eqπ x)) id⊢

    sB : (t : ⟨ N .transition ⟩)
      → (⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy Eqr
        ⊢ ⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy ⟦_⟧N)
      → ⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy Eqr
        ⊗ Trace (Sum.inl tt) ⊢ A.Trace (N .src t) ⊗ (A.Parse *)
    sB t z = ⊗-map (A.STEP t) id⊢ ∘⊢ ⊗-assoc⁻
      ∘⊢ ⊗-map id⊢ (from*NFA (Sum.inr (N .dst t)) ∘⊢ ⟜-app)
      ∘⊢ ⊗-assoc ∘⊢ ⊗-map (A.step-out t Eq.refl ∘⊢ z) id⊢

    sC : (t : ⟨ N .transition ⟩)
      → (Eqr (N .dst t) ⊗ Trace (Sum.inl tt)
        ⊢ A.Trace (N .dst t) ⊗ (A.Parse *))
      → ⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy Eqr
        ⊗ Trace (Sum.inl tt) ⊢ A.Trace (N .src t) ⊗ (A.Parse *)
    sC t z = ⊗-map (A.STEP t) id⊢ ∘⊢ ⊗-assoc⁻ ∘⊢ ⊗-map id⊢ z ∘⊢ ⊗-assoc
      ∘⊢ ⊗-map (A.step-out t Eq.refl) id⊢

    sD : (t : ⟨ N .transition ⟩)
      → ((literal (N .label t) ⊗ Eqr (N .dst t)) ⊗ Trace (Sum.inl tt)
        ⊢ (literal (N .label t) ⊗ Eqr (N .dst t)) ⊗ Trace (Sum.inl tt))
      → ⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy Eqr
        ⊗ Trace (Sum.inl tt) ⊢ A.Trace (N .src t) ⊗ (A.Parse *)
    sD t z = ⊗-map (A.STEP t) id⊢
      ∘⊢ ⊗-map (⊗-map id⊢ (eqπ (N .dst t))) F*
      ∘⊢ z ∘⊢ ⊗-map (A.step-out t Eq.refl) id⊢

    sE : (t : ⟨ N .transition ⟩)
      → (⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy Eqr
        ⊢ ⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy A.Trace)
      → ⟦ A.branch (N .src t) (A.step t Eq.refl) ⟧TheoryTy Eqr
        ⊗ Trace (Sum.inl tt) ⊢ A.Trace (N .src t) ⊗ (A.Parse *)
    sE t z = ⊗-map (roll ∘⊢ σ⊕ (A.step t Eq.refl) ∘⊢ z) F*

  nested-induction : ∀ q
    → from*NFA (Sum.inr q) ∘⊢ ⟜-intro⁻ (N→⟜ q) ≡ ⊗-map id⊢ F*
  nested-induction q =
    sym (nL-uncurry q id⊢)
    ∙ cong ⟜-intro⁻ (equalizer-ind A.TraceTy C⟜ nL nR pf q)
    ∙ nR-uncurry q id⊢
    where
    pf : ∀ q → nL q ∘⊢ roll ∘⊢ map (A.TraceTy q) eqπ
             ≡ nR q ∘⊢ roll ∘⊢ map (A.TraceTy q) eqπ
    pf q = ⊕ᴰ≡ _ _ λ where
      (A.stop acc) → cong ⟜-intro
        ( nL-uncurry q (hOf q (A.stop acc))
        ∙ cong (nA q) (⟜-β (U-acc q acc))
        ∙ cong (λ z → nB q acc z (lowerTy ∘⊢ lowerTy)) (⊗-unit-l-nat↑ F*)
        ∙ cong (λ z → nC q acc z (lowerTy ∘⊢ lowerTy))
               (⊗-unit-l⁻∘l {A = A.Parse *})
        ∙ sym (nR-uncurry q (hOf q (A.stop acc))) )
      (A.step t Eq.refl) → cong ⟜-intro
        ( nL-uncurry (N .src t) (hOf (N .src t) (A.step t Eq.refl))
        ∙ cong (nA (N .src t)) (⟜-β (U-step t))
        ∙ cong (sA t) (map-step from*NFA t Eq.refl)
        ∙ cong (sB t) (A.map-step (λ x → N→⟜ x ∘⊢ eqπ x) t Eq.refl)
        ∙ cong (sC t) (sym (nL-uncurry (N .dst t) (eqπ (N .dst t))))
        ∙ cong (sC t) (cong ⟜-intro⁻ (eq-π-pf (nL (N .dst t)) (nR (N .dst t))))
        ∙ cong (sC t) (nR-uncurry (N .dst t) (eqπ (N .dst t)))
        ∙ cong (sD t) (⊗-assoc⁻∘⊗-assoc {A = literal (N .label t)}
                          {B = Eqr (N .dst t)} {C = Trace (Sum.inl tt)})
        ∙ cong (sE t) (sym (A.map-step eqπ t Eq.refl))
        ∙ sym (nR-uncurry (N .src t) (hOf (N .src t) (A.step t Eq.refl))) )
      (A.stepε t Eq.refl) → cong ⟜-intro
        ( nL-uncurry (N .ε-src t) (hOf (N .ε-src t) (A.stepε t Eq.refl))
        ∙ cong (nA (N .ε-src t)) (⟜-β (U-ε t))
        ∙ cong (εB t) (sym (nL-uncurry (N .ε-dst t)
                              (eqπ (N .ε-dst t) ∘⊢ lowerTy)))
        ∙ cong (εB t) (cong ⟜-intro⁻
            (cong (_∘⊢ lowerTy) (eq-π-pf (nL (N .ε-dst t)) (nR (N .ε-dst t)))))
        ∙ cong (εB t) (nR-uncurry (N .ε-dst t) (eqπ (N .ε-dst t) ∘⊢ lowerTy))
        ∙ sym (nR-uncurry (N .ε-src t) (hOf (N .ε-src t) (A.stepε t Eq.refl))) )

  private
    nilW : ∀ {ℓD} {D : TheoryTy ℓD tt}
      → (D ⊢ ⟦ starBranch A.Parse false ⟧TheoryTy (λ _ → A.Parse *))
      → D ⊢ A.Parse *
    nilW z = roll ∘⊢ σ⊕ false ∘⊢ z

    consA : (A.Trace (N .init) ⊗ Trace (Sum.inl tt)
            ⊢ A.Trace (N .init) ⊗ (A.Parse *))
      → ⟦ starBranch A.Parse true ⟧TheoryTy (λ _ → Trace (Sum.inl tt))
      ⊢ A.Parse *
    consA z = roll ∘⊢ σ⊕ true
      ∘⊢ ⟦⊗e⟧⁻ {A = λ _ → A.Parse *} (k A.Parse) (Var tt)
      ∘⊢ ⊗-map liftTy liftTy ∘⊢ z ∘⊢ ⊗-map lowerTy lowerTy
      ∘⊢ ⟦⊗e⟧ {A = λ _ → Trace (Sum.inl tt)} (k A.Parse) (Var tt)

    consW : ∀ {ℓD} {D : TheoryTy ℓD tt}
      → (D ⊢ ⟦ starBranch A.Parse true ⟧TheoryTy (λ _ → A.Parse *))
      → (⟦ starBranch A.Parse true ⟧TheoryTy (λ _ → Trace (Sum.inl tt)) ⊢ D)
      → ⟦ starBranch A.Parse true ⟧TheoryTy (λ _ → Trace (Sum.inl tt))
      ⊢ A.Parse *
    consW z d = roll ∘⊢ σ⊕ true ∘⊢ z ∘⊢ d

    consB : (⟦ starBranch A.Parse true ⟧TheoryTy (λ _ → Trace (Sum.inl tt))
            ⊢ ⟦ starBranch A.Parse true ⟧TheoryTy (λ _ → Trace (Sum.inl tt)))
      → ⟦ starBranch A.Parse true ⟧TheoryTy (λ _ → Trace (Sum.inl tt))
      ⊢ A.Parse *
    consB z = roll ∘⊢ σ⊕ true
      ∘⊢ map (starBranch A.Parse true) (λ _ → F*) ∘⊢ z

  F*-homo : ∀ (_ : Unit) → F* ∘⊢ N*Alg tt
                         ≡ roll ∘⊢ map (StarCode A.Parse) (λ _ → F*)
  F*-homo _ = ⊕ᴰ≡ _ _ λ where
    false → cong nilW (sym (⊗e-ε-map _ (λ _ → F*)))
    true →
      cong consA (nested-induction (N .init))
      ∙ cong (λ z → consW z (⟦⊗e⟧ {A = λ _ → Trace (Sum.inl tt)}
                               (k A.Parse) (Var tt)))
             (sym (⟦⊗e⟧⁻-nat (k A.Parse) (Var tt)
                    {A = λ _ → Trace (Sum.inl tt)}
                    {B = λ _ → A.Parse *} (λ _ → F*)))
      ∙ cong consB (⟦⊗e⟧-η (k A.Parse) (Var tt)
                      {A = λ _ → Trace (Sum.inl tt)})

  *NFA-sec : F* ∘⊢ T* ≡ id⊢
  *NFA-sec =
    rec-section (λ _ → StarCode A.Parse) N*Alg (λ _ → F*) F*-homo tt

  *NFA≅ : Parse ≅ (A.Parse *)
  *NFA≅ .fun = from*NFA (Sum.inl tt)
  *NFA≅ .inv = T*
  *NFA≅ .sec = *NFA-sec
  *NFA≅ .ret = *NFA-ret (Sum.inl tt)
