open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Sum.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Sigma

open import Theory.Base σeq V vs 𝒫

private variable ℓA ℓB ℓY ℓZ : Level

⊕ᴰ : ∀ {s} (Y : Type ℓY) → (Y → TheoryTy ℓA s) → TheoryTy (ℓ-max ℓY ℓA) s
⊕ᴰ Y A m = Σ[ y ∈ Y ] A y m

syntax ⊕ᴰ Y (λ y → A) = ⊕[ y ∈ Y ] A
infix 8 ⊕ᴰ

module _ {s} {Y : Type ℓY} {A : Y → TheoryTy ℓA s} where
  σ⊕ : ∀ (y : Y) → A y ⊢ ⊕[ y ∈ Y ] A y
  σ⊕ = λ y m z → y , z

module _ {s : S} {Y : Type ℓY}
  {A : TheoryTy ℓA s}
  {B : Y → TheoryTy ℓB s}
  where
  ⊕ᴰ-elim : (∀ y → B y ⊢ A) → ⊕[ y ∈ Y ] B y ⊢ A
  ⊕ᴰ-elim = λ z m z₁ → z (z₁ .fst) m (z₁ .snd)

  ⊕ᴰ≡ : (f f' : ⊕[ y ∈ Y ] B y ⊢ A)
    → (∀ y → f ∘⊢ σ⊕ y ≡ f' ∘⊢ σ⊕ y)
    → f ≡ f'
  ⊕ᴰ≡ f f' f≡ i m z = f≡ (z .fst) i m (z .snd)

module _ {Y : Type ℓY}{s}
  {A : Y → TheoryTy ℓA s} {B : Y → TheoryTy ℓB s}
  (e : (y : Y) → A y ⊢ B y)
  where
  map⊕ᴰ : ⊕[ y ∈ Y ] A y ⊢ ⊕[ y ∈ Y ] B y
  map⊕ᴰ = ⊕ᴰ-elim λ y → σ⊕ y ∘⊢ e y

module _ {Y : Type ℓY}{Z : Type ℓZ}{s}
  {A : Y → TheoryTy ℓA s} {B : Z → TheoryTy ℓB s}
  (f : Y → Z)
  (e : (y : Y) → A y ⊢ B (f y))
  where
  mapFst⊕ᴰ : ⊕[ y ∈ Y ] A y ⊢ ⊕[ z ∈ Z ] B z
  mapFst⊕ᴰ = ⊕ᴰ-elim (λ y → σ⊕ (f y)) ∘⊢ map⊕ᴰ e
