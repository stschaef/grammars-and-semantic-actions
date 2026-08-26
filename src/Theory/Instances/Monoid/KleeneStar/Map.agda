{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `_*` is a functor, and it takes isomorphisms to isomorphisms.

   The action is the fold that rebuilds the list one cell at a time; both
   round trips are `rec-section`, whose homomorphism law is the `⟦⊗e⟧`
   naturality that `Convolution` already states. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.WildCat.LocallySmall.Base
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.KleeneStar.Map
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Unit using (Unit ; tt)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Convolution Alphabet isSetAlphabet
  using (⟦⊗e⟧ ; ⟦⊗e⟧⁻ ; ⟦⊗e⟧-η ; ⟦⊗e⟧⁻-nat ; ⊗e-ε→ ; ⊗e-ε← ; ⊗e-ε-map)

open WildCatNotation
open WildCatIso

private variable ℓA ℓB : Level

module _ {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} where

  *Alg : (f : A ⊢ B) (_ : Unit)
    → ⟦ StarCode A ⟧TheoryTy (λ _ → B *) ⊢ B *
  *Alg f _ = ⊕ᴰ-elim λ where
    false → roll ∘⊢ σ⊕ false ∘⊢ ⊗e-ε← _ ∘⊢ ⊗e-ε→ _
    true → roll ∘⊢ σ⊕ true ∘⊢ ⟦⊗e⟧⁻ {A = λ _ → B *} (k B) (Var tt)
             ∘⊢ ⊗-map (liftTy ∘⊢ f ∘⊢ lowerTy) (liftTy ∘⊢ lowerTy)
             ∘⊢ ⟦⊗e⟧ {A = λ _ → B *} (k A) (Var tt)

  *-map : (f : A ⊢ B) → A * ⊢ B *
  *-map f = rec (λ _ → StarCode A) (*Alg f) tt

-- A retraction of the elements is a retraction of the lists.
module _ {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  (f : A ⊢ B) (h : B ⊢ A) (hf : h ∘⊢ f ≡ id⊢) where

  private
    ψ : Unit → B * ⊢ A *
    ψ _ = *-map h

    nilW : ∀ {ℓD} {D : TheoryTy ℓD tt}
      → (D ⊢ ⟦ starBranch A false ⟧TheoryTy (λ _ → A *)) → D ⊢ A *
    nilW z = roll ∘⊢ σ⊕ false ∘⊢ z

    consH : (A ⊢ A)
      → ⟦ starBranch A true ⟧TheoryTy (λ _ → B *) ⊢ A *
    consH z = roll ∘⊢ σ⊕ true ∘⊢ ⟦⊗e⟧⁻ {A = λ _ → A *} (k A) (Var tt)
      ∘⊢ ⊗-map (liftTy ∘⊢ z ∘⊢ lowerTy)
               (liftTy ∘⊢ *-map h ∘⊢ lowerTy)
      ∘⊢ ⟦⊗e⟧ {A = λ _ → B *} (k A) (Var tt)

    consW : ∀ {ℓD} {D : TheoryTy ℓD tt}
      → (D ⊢ ⟦ starBranch A true ⟧TheoryTy (λ _ → A *))
      → (⟦ starBranch A true ⟧TheoryTy (λ _ → B *) ⊢ D)
      → ⟦ starBranch A true ⟧TheoryTy (λ _ → B *) ⊢ A *
    consW z d = roll ∘⊢ σ⊕ true ∘⊢ z ∘⊢ d

    consB : (⟦ starBranch A true ⟧TheoryTy (λ _ → B *)
            ⊢ ⟦ starBranch A true ⟧TheoryTy (λ _ → B *))
      → ⟦ starBranch A true ⟧TheoryTy (λ _ → B *) ⊢ A *
    consB z = roll ∘⊢ σ⊕ true ∘⊢ map (starBranch A true) ψ ∘⊢ z

    ψ-homo : ∀ (u : Unit) → ψ u ∘⊢ *Alg f tt
                          ≡ roll ∘⊢ map (StarCode A) ψ
    ψ-homo _ = ⊕ᴰ≡ _ _ λ where
      false → cong nilW (sym (⊗e-ε-map _ ψ))
      true →
        cong consH hf
        ∙ cong (λ z → consW z (⟦⊗e⟧ {A = λ _ → B *} (k A) (Var tt)))
               (sym (⟦⊗e⟧⁻-nat (k A) (Var tt)
                      {A = λ _ → B *} {B = λ _ → A *} ψ))
        ∙ cong consB (⟦⊗e⟧-η (k A) (Var tt) {A = λ _ → B *})

  *-map-section : *-map h ∘⊢ *-map f ≡ id⊢
  *-map-section = rec-section (λ _ → StarCode A) (*Alg f) ψ ψ-homo tt


module _ {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} (A≅B : A ≅ B) where
  -- ...so an isomorphism of elements is an isomorphism of lists.
  *≅ : (A *) ≅ (B *)
  *≅ .fun = *-map (A≅B .fun)
  *≅ .inv = *-map (A≅B .inv)
  *≅ .sec = *-map-section (A≅B .inv) (A≅B .fun) (A≅B .sec)
  *≅ .ret = *-map-section (A≅B .fun) (A≅B .inv) (A≅B .ret)
