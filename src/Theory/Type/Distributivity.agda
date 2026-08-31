open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Distributivity
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Sigma
open import Cubical.WildCat.LocallySmall.Base

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Operation.Base σeq V vs 𝒫
open import Theory.Type.Sum.Base σeq V vs 𝒫
open import Theory.Type.Product.Base σeq V vs 𝒫

open WildCatNotation
open WildCatIso

private variable ℓA ℓY : Level

module _ (o : σ .ops) {Y : arities σ o → Type ℓY}
  (A : (a : arities σ o) → Y a → TheoryTy ℓA (σ .sortOf o a)) where

  ⊗⊕ᴰ-dist : ⊗ᵘ[ o ] (λ a → ⊕[ y ∈ Y a ] A a y)
           ⊢ ⊕[ f ∈ ((a : arities σ o) → Y a) ] ⊗ᵘ[ o ] (λ a → A a (f a))
  ⊗⊕ᴰ-dist m (ms , p , g) = (λ a → g a .fst) , ms , p , λ a → g a .snd

  ⊗⊕ᴰ-dist⁻ : ⊕[ f ∈ ((a : arities σ o) → Y a) ] ⊗ᵘ[ o ] (λ a → A a (f a))
            ⊢ ⊗ᵘ[ o ] (λ a → ⊕[ y ∈ Y a ] A a y)
  ⊗⊕ᴰ-dist⁻ m (f , ms , p , g) = ms , p , λ a → f a , g a

  ⊗⊕ᴰ-dist≅ : (⊗ᵘ[ o ] (λ a → ⊕[ y ∈ Y a ] A a y))
            ≅ (⊕[ f ∈ ((a : arities σ o) → Y a) ] ⊗ᵘ[ o ] (λ a → A a (f a)))
  ⊗⊕ᴰ-dist≅ .fun = ⊗⊕ᴰ-dist
  ⊗⊕ᴰ-dist≅ .inv = ⊗⊕ᴰ-dist⁻
  ⊗⊕ᴰ-dist≅ .sec = refl
  ⊗⊕ᴰ-dist≅ .ret = refl

module _ (o : σ .ops) {Y : Type ℓY}
  (A : (a : arities σ o) → Y → TheoryTy ℓA (σ .sortOf o a)) where

  ⊗&ᴰ-dist : ⊗ᵘ[ o ] (λ a → &[ y ∈ Y ] A a y) ⊢ &[ y ∈ Y ] ⊗ᵘ[ o ] (λ a → A a y)
  ⊗&ᴰ-dist = &ᴰ-intro λ y → ⊗map o λ a → π {A = A a} y
