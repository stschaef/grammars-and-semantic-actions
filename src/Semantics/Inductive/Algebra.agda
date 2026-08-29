{-# OPTIONS --lossy-unification #-}
{- Algebras for a strictly positive functor, and initial algebras.

   Algebras for `F : X → Functor X` form a category, and an initial
   algebra is exactly an initial object of it. So `rec` is the centre
   of a contraction and the induction principle is that contraction's
   uniqueness — no `{-# TERMINATING #-}` and no hand-rolled η, in
   contrast to `Grammar.Inductive.Indexed`.

   Lambek's lemma is then a theorem rather than a definition.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Semantics.Model

module Semantics.Inductive.Algebra {ℓ ℓ' ℓX} {Gen : hSet ℓX}
  (M : GrammarModel ℓ ℓ' ℓX Gen) where

open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Initial

open import Semantics.Notation M
open import Semantics.Inductive.Functor M

private
  variable
    X : Type ℓX

module _ {X : Type ℓX} (F : X → Functor X) where

  Algebra : (X → Grammar) → Type (ℓ-max ℓX ℓ')
  Algebra A = ∀ x → ⟦ F x ⟧ A ⊢ A x

  AlgOb : Type (ℓ-max ℓX (ℓ-max ℓ ℓ'))
  AlgOb = Σ[ A ∈ (X → Grammar) ] Algebra A

  module _ (A B : AlgOb) where
    isHomo : (∀ x → A .fst x ⊢ B .fst x) → Type (ℓ-max ℓX ℓ')
    isHomo ϕ = ∀ x → ϕ x ∘g A .snd x ≡ B .snd x ∘g map (F x) ϕ

    isPropIsHomo : ∀ ϕ → isProp (isHomo ϕ)
    isPropIsHomo ϕ = isPropΠ λ x → isSetHom _ _

    AlgHom : Type (ℓ-max ℓX ℓ')
    AlgHom = Σ[ ϕ ∈ (∀ x → A .fst x ⊢ B .fst x) ] isHomo ϕ

    isSetAlgHom : isSet AlgHom
    isSetAlgHom =
      isSetΣ (isSetΠ λ x → isSetHom) λ ϕ → isProp→isSet (isPropIsHomo ϕ)

  AlgHom≡ : {A B : AlgOb} {ϕ ψ : AlgHom A B} → ϕ .fst ≡ ψ .fst → ϕ ≡ ψ
  AlgHom≡ {A = A} {B = B} = Σ≡Prop (isPropIsHomo A B)

  ALGEBRA : Category (ℓ-max ℓX (ℓ-max ℓ ℓ')) (ℓ-max ℓX ℓ')
  ALGEBRA .Category.ob = AlgOb
  ALGEBRA .Category.Hom[_,_] = AlgHom
  ALGEBRA .Category.id {A} .fst x = id
  ALGEBRA .Category.id {A} .snd x =
    ∘g-idL (A .snd x)
    ∙ sym (cong (A .snd x ∘g_) (map-id (F x)) ∙ ∘g-idR (A .snd x))
  ALGEBRA .Category._⋆_ {A} {B} {C} (ϕ , p) (ψ , q) .fst x = ψ x ∘g ϕ x
  ALGEBRA .Category._⋆_ {A} {B} {C} (ϕ , p) (ψ , q) .snd x =
    ∘g-assoc (ψ x) (ϕ x) (A .snd x)
    ∙ cong (ψ x ∘g_) (p x)
    ∙ sym (∘g-assoc (ψ x) (B .snd x) (map (F x) ϕ))
    ∙ cong (_∘g map (F x) ϕ) (q x)
    ∙ ∘g-assoc (C .snd x) (map (F x) ψ) (map (F x) ϕ)
    ∙ cong (C .snd x ∘g_) (sym (map-∘ (F x) ψ ϕ))
  ALGEBRA .Category.⋆IdL f = AlgHom≡ (funExt λ x → ∘g-idR (f .fst x))
  ALGEBRA .Category.⋆IdR f = AlgHom≡ (funExt λ x → ∘g-idL (f .fst x))
  ALGEBRA .Category.⋆Assoc f g h =
    AlgHom≡ (funExt λ x → sym (∘g-assoc (h .fst x) (g .fst x) (f .fst x)))
  ALGEBRA .Category.isSetHom {A} {B} = isSetAlgHom A B

  -- | An initial algebra is an initial object of the algebra category.
  InitialAlgebra : Type (ℓ-max ℓX (ℓ-max ℓ ℓ'))
  InitialAlgebra = Initial ALGEBRA

-- | A model has all initial algebras when every strictly positive
--   functor code has one.
HasInitialAlgebras : Type (ℓ-max (ℓ-suc ℓX) (ℓ-max ℓ ℓ'))
HasInitialAlgebras =
  {X : Type ℓX} (F : X → Functor X) → InitialAlgebra F

------------------------------------------------------------------------
-- What an initial algebra gives you
------------------------------------------------------------------------

module InitialAlgebraNotation {X : Type ℓX} {F : X → Functor X}
  (I : InitialAlgebra F) where

  μ : X → Grammar
  μ = I .fst .fst

  roll : Algebra F μ
  roll = I .fst .snd

  module _ {A : X → Grammar} (α : Algebra F A) where
    rec : ∀ x → μ x ⊢ A x
    rec = I .snd (A , α) .fst .fst

    rec-homo : ∀ x → rec x ∘g roll x ≡ α x ∘g map (F x) rec
    rec-homo = I .snd (A , α) .fst .snd

    -- Uniqueness: any homomorphism out of the initial algebra is rec.
    ind : (ϕ : AlgHom F (μ , roll) (A , α)) → rec ≡ ϕ .fst
    ind ϕ = cong fst (I .snd (A , α) .snd ϕ)

  -- Two endomorphisms of the initial algebra agree.
  ind-id : (ϕ : AlgHom F (μ , roll) (μ , roll)) → ϕ .fst ≡ λ x → id
  ind-id ϕ =
    cong fst (isContr→isProp (I .snd (μ , roll)) ϕ (Category.id (ALGEBRA F)))

  ------------------------------------------------------------------
  -- Lambek's lemma: roll is an isomorphism.
  ------------------------------------------------------------------
  private
    unrollAlg : Algebra F (λ x → ⟦ F x ⟧ μ)
    unrollAlg x = map (F x) roll

  unroll : ∀ x → μ x ⊢ ⟦ F x ⟧ μ
  unroll = rec unrollAlg

  private
    unroll-roll : ∀ x → unroll x ∘g roll x
                      ≡ map (F x) roll ∘g map (F x) unroll
    unroll-roll = rec-homo unrollAlg

    rollUnroll : AlgHom F (μ , roll) (μ , roll)
    rollUnroll .fst x = roll x ∘g unroll x
    rollUnroll .snd x =
      ∘g-assoc (roll x) (unroll x) (roll x)
      ∙ cong (roll x ∘g_) (unroll-roll x ∙ sym (map-∘ (F x) roll unroll))

  Lambek-sec : ∀ x → roll x ∘g unroll x ≡ id
  Lambek-sec x = funExt⁻ (ind-id rollUnroll) x

  Lambek-ret : ∀ x → unroll x ∘g roll x ≡ id
  Lambek-ret x =
    unroll-roll x
    ∙ sym (map-∘ (F x) roll unroll)
    ∙ cong (map (F x)) (funExt Lambek-sec)
    ∙ map-id (F x)
