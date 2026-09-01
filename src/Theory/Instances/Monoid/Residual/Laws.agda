{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `⟜-intro⁻` spends the splitting's equation and `⟜-post` does not;
   matching that equation is the whole proof. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Residual.Laws
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (_⟜_ ; ⟜-intro ; ⟜-intro⁻ ; ⟜-app ; ⟜-post ; ⟜-precomp)

private variable ℓ ℓ' ℓ'' ℓ''' : Level

module _ {A : TheoryTy ℓ tt} {B : TheoryTy ℓ' tt} {C : TheoryTy ℓ'' tt} where

  -- Not `refl`: the sides apply `X` on either side of the splitting's cast.
  ⟜-post-intro⁻ : {C' : TheoryTy ℓ''' tt} (X : C ⊢ C') (f : A ⊢ C ⟜ B)
    → ⟜-intro⁻ (⟜-post X ∘⊢ f) ≡ X ∘⊢ ⟜-intro⁻ f
  ⟜-post-intro⁻ X f = funExt λ m → funExt λ where
    (ms , Eq.refl , (a , (b , _))) → refl

  ⟜-post-precomp-intro⁻ : {C' : TheoryTy ℓ''' tt} {ℓ⁗ : Level}
    {B' : TheoryTy ℓ⁗ tt} (X : C ⊢ C') (g : B' ⊢ B) (f : A ⊢ C ⟜ B)
    → ⟜-intro⁻ (⟜-post X ∘⊢ ⟜-precomp g ∘⊢ f)
      ≡ X ∘⊢ ⟜-intro⁻ f ∘⊢ ⊗-map id⊢ g
  ⟜-post-precomp-intro⁻ X g f = funExt λ m → funExt λ where
    (ms , Eq.refl , (a , (b , _))) → refl

  ⟜-precomp-intro⁻ : {B' : TheoryTy ℓ''' tt} (g : B' ⊢ B) (f : A ⊢ C ⟜ B)
    → ⟜-intro⁻ {A = A} {B = B'} {C = C} (⟜-precomp g ∘⊢ f)
      ≡ ⟜-intro⁻ f ∘⊢ ⊗-map (id⊢ {A = A}) g
  ⟜-precomp-intro⁻ g f = refl

  ⟜-intro⁻-nat : {A' : TheoryTy ℓ''' tt} (f : A ⊢ C ⟜ B) (h : A' ⊢ A)
    → ⟜-intro⁻ {A = A'} {B = B} {C = C} (f ∘⊢ h)
      ≡ ⟜-intro⁻ f ∘⊢ ⊗-map h (id⊢ {A = B})
  ⟜-intro⁻-nat f h = refl

  ⟜-app-intro⁻ : {A' : TheoryTy ℓ''' tt} (f : A' ⊢ C ⟜ B)
    → ⟜-app {B = B} {C = C} ∘⊢ ⊗-map f id⊢ ≡ ⟜-intro⁻ f
  ⟜-app-intro⁻ f = refl
