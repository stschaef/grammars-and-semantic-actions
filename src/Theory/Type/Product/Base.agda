open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Product.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.WildCat.LocallySmall.Base

open import Theory.Base σeq V vs 𝒫

open WildCatNotation
open WildCatIso

private variable ℓA ℓB ℓY : Level

&ᴰ : ∀ {s} (Y : Type ℓY) → (Y → TheoryTy ℓA s) → TheoryTy (ℓ-max ℓY ℓA) s
&ᴰ Y A m = (y : Y) → A y m

syntax &ᴰ Y (λ y → A) = &[ y ∈ Y ] A
infix 7 &ᴰ

module _ {s} {Y : Type ℓY} {A : Y → TheoryTy ℓA s} where
  π : ∀ (y : Y) → (&[ y ∈ Y ] A y) ⊢ A y
  π = λ y m z → z y

module _ {s : S} {Y : Type ℓY}
  {A : TheoryTy ℓA s}
  {B : Y → TheoryTy ℓB s}
  where
  &ᴰ-intro : (∀ y → A ⊢ B y) → A ⊢ &[ y ∈ Y ] B y
  &ᴰ-intro f m a y = f y m a

  &ᴰ≡ : (f f' : A ⊢ &[ y ∈ Y ] B y)
    → (∀ y → π y ∘⊢ f ≡ π y ∘⊢ f')
    → f ≡ f'
  &ᴰ≡ f f' f≡ i m z y = f≡ y i m z

module _ {Y : Type ℓY} {s} {A : TheoryTy ℓA s} where
  Δ : A ⊢ &[ y ∈ Y ] A
  Δ = &ᴰ-intro (λ _ → id⊢)

module _ {Y : Type ℓY}{s}
  {A : Y → TheoryTy ℓA s} {B : Y → TheoryTy ℓB s}
  (e : (y : Y) → A y ⊢ B y)
  where
  map&ᴰ : &[ y ∈ Y ] A y ⊢ &[ y ∈ Y ] B y
  map&ᴰ = &ᴰ-intro λ y → e y ∘⊢ π y

module _ {s} {Y : Type ℓY}
  {A : Y → TheoryTy ℓA s} {B : Y → TheoryTy ℓB s}
  (A≅B : ∀ (y : Y) → A y ≅ B y)
  where
  &ᴰ≅ : (&[ y ∈ Y ] A y) ≅ (&[ y ∈ Y ] B y)
  &ᴰ≅ .fun = λ m z y → A≅B y .fun m (z y)
  &ᴰ≅ .inv = λ m z y → A≅B y .inv m (z y)
  &ᴰ≅ .sec = &ᴰ≡ _ _ λ y → cong (_∘⊢ π y) (A≅B y .sec)
  &ᴰ≅ .ret = &ᴰ≡ _ _ λ y → cong (_∘⊢ π y) (A≅B y .ret)
