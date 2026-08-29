{-# OPTIONS --lossy-unification #-}
{- The Kleene star, in an arbitrary model with initial algebras.

   `A *` is the initial algebra of `B ↦ ε ⊕ (A ⊗ B)`, so `fold*` is
   `rec` and the uniqueness of folds is `ind`. The two β laws are
   derived from `rec-homo` and the β law of ⊕ᴰ.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Semantics.Model

module Semantics.Inductive.KleeneStar {ℓ ℓ' ℓX} {Gen : hSet ℓX}
  (M : GrammarModel ℓ ℓ' ℓX Gen) where

open import Cubical.Data.Bool using (true; false)
open import Cubical.Data.Unit using (Unit*; tt*)

open import Semantics.Notation M
open import Semantics.Inductive.Functor M
open import Semantics.Inductive.Algebra M

module Star (A : Grammar) where
  -- ε ⊕ (A ⊗ -), as a code.
  *Ty : Unit* {ℓX} → Functor (Unit* {ℓX})
  *Ty _ = ⊕e Two λ where
    (lift true) → k ε
    (lift false) → k A ⊗e Var tt*

  module WithFix (I : InitialAlgebra *Ty) where
    open InitialAlgebraNotation I

    infix 30 _*
    _* : Grammar
    _* = μ tt*

    NIL : ε ⊢ _*
    NIL = roll tt* ∘g σ (lift true)

    CONS : A ⊗ _* ⊢ _*
    CONS = roll tt* ∘g σ (lift false)

    module _ {B : Grammar} (nil : ε ⊢ B) (cons : A ⊗ B ⊢ B) where
      private
        alg : Algebra *Ty (λ _ → B)
        alg _ = ⊕ᴰ-elim λ where
          (lift true) → nil
          (lift false) → cons

      fold* : _* ⊢ B
      fold* = rec alg tt*

      private
        homo : fold* ∘g roll tt* ≡ alg tt* ∘g map (*Ty tt*) (rec alg)
        homo = rec-homo alg tt*

      fold*-nil : fold* ∘g NIL ≡ nil
      fold*-nil =
        sym (∘g-assoc fold* (roll tt*) (σ (lift true)))
        ∙ cong (_∘g σ (lift true)) homo
        ∙ ∘g-assoc (alg tt*) (map (*Ty tt*) (rec alg)) (σ (lift true))
        ∙ cong (alg tt* ∘g_) (⊕ᴰ-β _ (lift true))
        ∙ cong (alg tt* ∘g_) (∘g-idR (σ (lift true)))
        ∙ ⊕ᴰ-β _ (lift true)

      fold*-cons : fold* ∘g CONS ≡ cons ∘g (id ,⊗ fold*)
      fold*-cons =
        sym (∘g-assoc fold* (roll tt*) (σ (lift false)))
        ∙ cong (_∘g σ (lift false)) homo
        ∙ ∘g-assoc (alg tt*) (map (*Ty tt*) (rec alg)) (σ (lift false))
        ∙ cong (alg tt* ∘g_) (⊕ᴰ-β _ (lift false))
        ∙ sym (∘g-assoc (alg tt*) (σ (lift false)) (id ,⊗ fold*))
        ∙ cong (_∘g (id ,⊗ fold*)) (⊕ᴰ-β _ (lift false))


      -- Uniqueness of folds: this is `ind`, repackaged.
      fold*-unique : (h : _* ⊢ B)
        → h ∘g NIL ≡ nil
        → h ∘g CONS ≡ cons ∘g (id ,⊗ h)
        → fold* ≡ h
      fold*-unique h hnil hcons = funExt⁻ (ind alg hHomo) tt*
        where
        mapAlg = map (*Ty tt*) (λ _ → h)

        rhs-nil : (alg tt* ∘g mapAlg) ∘g σ (lift true) ≡ nil
        rhs-nil =
          ∘g-assoc (alg tt*) mapAlg (σ (lift true))
          ∙ cong (alg tt* ∘g_)
                 (⊕ᴰ-β _ (lift true) ∙ ∘g-idR (σ (lift true)))
          ∙ ⊕ᴰ-β _ (lift true)

        rhs-cons : (alg tt* ∘g mapAlg) ∘g σ (lift false)
                 ≡ cons ∘g (id ,⊗ h)
        rhs-cons =
          ∘g-assoc (alg tt*) mapAlg (σ (lift false))
          ∙ cong (alg tt* ∘g_) (⊕ᴰ-β _ (lift false))
          ∙ sym (∘g-assoc (alg tt*) (σ (lift false)) (id ,⊗ h))
          ∙ cong (_∘g (id ,⊗ h)) (⊕ᴰ-β _ (lift false))

        hHomo : AlgHom *Ty (μ , roll) ((λ _ → B) , alg)
        hHomo .fst _ = h
        hHomo .snd _ = ⊕ᴰ≡ λ where
          (lift true) →
            ∘g-assoc h (roll tt*) (σ (lift true)) ∙ hnil ∙ sym rhs-nil
          (lift false) →
            ∘g-assoc h (roll tt*) (σ (lift false)) ∙ hcons ∙ sym rhs-cons
