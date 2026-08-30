{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A word has at most one acceptance verdict from a given state: with
   `parse` for totality, `⊕[ b ] Trace b q` is a proposition, which is
   what makes `parse` and `print` inverse.

   An induction on one trace against a one-step unrolling of the other:
   two `step`s agree on the letter (`Precise.sameHead`), a `step` and a
   `stop` cannot describe one word (`Precise.ε∉lit⊗`), and two `stop`s
   carry acceptance equations meeting at `isAcc q`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Automaton.Disjoint
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.Unit using (tt ; tt*)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; ΣPathP)
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⊗⊕ᴰ-distR ; &⊕ᴰ-distR)
open import Theory.Instances.Monoid.Precise Alphabet isSetAlphabet
  using (ε∉lit⊗ ; sameHead)
open import Theory.Instances.Monoid.Automaton.Deterministic
  Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Unambiguous
  Alphabet isSetAlphabet using (unambiguous-Trace)
open import Theory.Type.HLevels MonEqns Alphabet (λ _ → tt) listPresentation
  using (isPropPathP)

private variable ℓQ : Level

module _ {Q : Type ℓQ} (Aut : DeterministicAutomaton Q) where
  open DeterministicAutomaton Aut

  module _ (b b' : Bool) where
    private
      Res : TheoryTy ℓ-zero tt
      Res = ⊕[ _ ∈ b ≡ b' ] ⊤Ty

      Carrier : Q → TheoryTy _ tt
      Carrier q = Trace b' q ⇒ Res

      -- two steps step by the same letter, so the recursive call at the
      -- common successor state supplies the verdict
      reState : (q : Q) (c d : Alphabet) → c ≡ d
        → Trace b' (δ q d) ⊢ Trace b' (δ q c)
      reState q c d p m t = subst (λ y → Trace b' (δ q y) m) (sym p) t

      stepStep : (q : Q) (c d : Alphabet)
        → (literal c ⊗ Carrier (δ q c)) & (literal d ⊗ Trace b' (δ q d))
        ⊢ Res
      stepStep q c d =
        ⊕ᴰ-elim
          (λ p →
            ⊕ᴰ-elim (λ pb → σ⊕ pb ∘⊢ ⊤Ty-intro)
            ∘⊢ ⊗⊕ᴰ-distR {C = λ _ → ⊤Ty}
            ∘⊢ (id⊢ ,⊗ (⇒-app ∘⊢ (id⊢ ,&p reState q c d p))))
        ∘⊢ sameHead c d

      stepStop : (q : Q) (c : Alphabet)
        → (literal c ⊗ Carrier (δ q c))
          & (⊕[ _ ∈ b' Eq.≡ isAcc q ] LiftTheoryTy ℓT εTy)
        ⊢ Res
      stepStop q c =
        ⊥Ty-elim ∘⊢ ε∉lit⊗ c
        ∘⊢ ((⊕ᴰ-elim (λ _ → lowerTy) ∘⊢ π₂) ,& π₁)

      stopStep : (q : Q)
        → εTy & (⊕[ c ∈ Alphabet ] (literal c ⊗ Trace b' (δ q c))) ⊢ Res
      stopStep q = ⊥Ty-elim ∘⊢ ⊕ᴰ-elim (λ c → ε∉lit⊗ c) ∘⊢ &⊕ᴰ-distR

      -- both stop: the two acceptance equations meet at `isAcc q`
      stopStop : (q : Q) → b Eq.≡ isAcc q
        → εTy & (⊕[ _ ∈ b' Eq.≡ isAcc q ] LiftTheoryTy ℓT εTy) ⊢ Res
      stopStop q p =
        ⊕ᴰ-elim (λ p' → σ⊕ (Eq.eqToPath p ∙ sym (Eq.eqToPath p')) ∘⊢ ⊤Ty-intro)
        ∘⊢ π₂

      disjAlg : (q : QL) → ⟦ TraceTy b q ⟧TheoryTy (λ x → Carrier (x .lower))
              ⊢ Carrier (q .lower)
      disjAlg (lift q) =
        ⊕-elim
          (⊕ᴰ-elim λ c →
            ⇒-intro
              (⊕-elim&
                (⊕ᴰ-elim (λ d → stepStep q c d) ∘⊢ &⊕ᴰ-distR)
                (stepStop q c)
              ∘⊢ (id⊢ ,&p unrollTrace b' q)))
          (⊕ᴰ-elim λ p →
            ⇒-intro
              (⊕-elim& (stopStep q) (stopStop q p)
              ∘⊢ (lowerTy ,&p unrollTrace b' q)))
        ∘⊢ fromCode b q

    TraceDisj : (q : Q) → Trace b q & Trace b' q ⊢ ⊕[ _ ∈ b ≡ b' ] ⊤Ty
    TraceDisj q = ⇒-intro⁻ (rec (TraceTy b) disjAlg (lift q))

  Runs : Q → TheoryTy _ tt
  Runs q = ⊕[ b ∈ Bool ] Trace b q

  unambiguous-Runs : (q : Q) (m : String) → isProp (Runs q m)
  unambiguous-Runs q m (b , t) (b' , t') =
    ΣPathP (b≡b' , isPropPathP _ (unambiguous-Trace Aut b q m) t t')
    where
    b≡b' : b ≡ b'
    b≡b' = TraceDisj b b' q m (t , t') .fst
