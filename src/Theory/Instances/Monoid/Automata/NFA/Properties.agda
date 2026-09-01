{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The two trace presentations agree at `true`: the maps are tag renamings. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.WildCat.LocallySmall.Base
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Automata.NFA.Properties
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Automata.NFA.Base Alphabet isSetAlphabet

open WildCatNotation
open WildCatIso

private variable ℓN : Level

module _ (N : NFA ℓN) where
  open NFA N
  private
    module Acc = NFA.Accepting N
    module PR = NFA.PotentiallyRejecting N

  AccAlg : Acc.TraceAlg (PR.Trace true)
  AccAlg q = ⊕ᴰ-elim λ where
    (Acc.stop x) → roll ∘⊢ σ⊕ PR.stop ∘⊢ σ⊕ (lift x)
    (Acc.step t Eq.refl) → roll ∘⊢ σ⊕ PR.step ∘⊢ σ⊕ (t , Eq.refl)
    (Acc.stepε t Eq.refl) → roll ∘⊢ σ⊕ PR.stepε ∘⊢ σ⊕ (t , Eq.refl)

  PRAlg : PR.TraceAlg true Acc.Trace
  PRAlg q = ⊕ᴰ-elim λ where
    PR.stop → roll ∘⊢ ⊕ᴰ-elim λ where (lift acc) → σ⊕ (Acc.stop acc)
    PR.step → roll ∘⊢ ⊕ᴰ-elim λ where (t , Eq.refl) → σ⊕ (Acc.step t Eq.refl)
    PR.stepε → roll ∘⊢ ⊕ᴰ-elim λ where (t , Eq.refl) → σ⊕ (Acc.stepε t Eq.refl)

  Acc→PR : ∀ q → Acc.Trace q ⊢ PR.Trace true q
  Acc→PR = rec Acc.TraceTy AccAlg

  PR→Acc : ∀ q → PR.Trace true q ⊢ Acc.Trace q
  PR→Acc = rec (PR.TraceTy true) PRAlg

  -- Homomorphisms on the nose, so `rec-section` closes both round trips; no equalizer induction.
  private
    Acc→PR-homo : ∀ q → Acc→PR q ∘⊢ PRAlg q
                      ≡ roll ∘⊢ map (PR.TraceTy true q) Acc→PR
    Acc→PR-homo q = ⊕ᴰ≡ _ _ λ where
      PR.stop → ⊕ᴰ≡ _ _ λ where (lift acc) → refl
      PR.step → ⊕ᴰ≡ _ _ λ where (t , Eq.refl) → refl
      PR.stepε → ⊕ᴰ≡ _ _ λ where (t , Eq.refl) → refl

    PR→Acc-homo : ∀ q → PR→Acc q ∘⊢ AccAlg q
                      ≡ roll ∘⊢ map (Acc.TraceTy q) PR→Acc
    PR→Acc-homo q = ⊕ᴰ≡ _ _ λ where
      (Acc.stop acc) → refl
      (Acc.step t Eq.refl) → refl
      (Acc.stepε t Eq.refl) → refl

  Trace≅ : ∀ (q : States) → Acc.Trace q ≅ PR.Trace true q
  Trace≅ q .fun = Acc→PR q
  Trace≅ q .inv = PR→Acc q
  Trace≅ q .sec = rec-section (PR.TraceTy true) PRAlg Acc→PR Acc→PR-homo q
  Trace≅ q .ret = rec-section Acc.TraceTy AccAlg PR→Acc PR→Acc-homo q

  Parse≅ : Acc.Parse ≅ PR.Parse
  Parse≅ = Trace≅ init
