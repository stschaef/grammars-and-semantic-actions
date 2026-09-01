open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Sum.Binary.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

import Cubical.Data.Sum as Sum
open import Cubical.WildCat.LocallySmall.Base

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Product.Binary.Base σeq V vs 𝒫 using (_&_)

open WildCatNotation
open WildCatIso

private
  variable
    ℓA ℓB ℓC ℓD : Level
    s : S
    A : TheoryTy ℓA s
    B : TheoryTy ℓB s
    C : TheoryTy ℓC s
    D : TheoryTy ℓD s

_⊕_ : ∀ {s} → TheoryTy ℓA s → TheoryTy ℓB s → TheoryTy (ℓ-max ℓA ℓB) s
(A ⊕ B) m = A m Sum.⊎ B m

infixr 18 _⊕_

inl : A ⊢ A ⊕ B
inl _ p = Sum.inl p

inr : A ⊢ B ⊕ A
inr _ p = Sum.inr p

⊕-elim : A ⊢ B → C ⊢ B → A ⊕ C ⊢ B
⊕-elim eA eB _ p = Sum.elim (λ pA → eA _ pA) (λ pB → eB _ pB) p

-- `&` distributes over `⊕`: both are pointwise.
⊕-elim& : {D : TheoryTy ℓD s} → D & A ⊢ B → D & C ⊢ B → D & (A ⊕ C) ⊢ B
⊕-elim& eA eB _ (d , Sum.inl p) = eA _ (d , p)
⊕-elim& eA eB _ (d , Sum.inr p) = eB _ (d , p)

⊕≡ : (f f' : A ⊕ C ⊢ B)
  → f ∘⊢ inl ≡ f' ∘⊢ inl → f ∘⊢ inr ≡ f' ∘⊢ inr
  → f ≡ f'
⊕≡ f f' f≡inl f≡inr = funExt λ m → funExt λ where
  (Sum.inl x) → funExt⁻ (funExt⁻ f≡inl _) x
  (Sum.inr x) → funExt⁻ (funExt⁻ f≡inr _) x

⊕-βl : (e₁ : A ⊢ C) (e₂ : B ⊢ C) → ⊕-elim e₁ e₂ ∘⊢ inl ≡ e₁
⊕-βl e₁ e₂ = refl

⊕-βr : (e₁ : A ⊢ C) (e₂ : B ⊢ C) → ⊕-elim e₁ e₂ ∘⊢ inr ≡ e₂
⊕-βr e₁ e₂ = refl

⊕-η : (e : A ⊕ B ⊢ C) → ⊕-elim (e ∘⊢ inl) (e ∘⊢ inr) ≡ e
⊕-η e i _ (Sum.inl x) = e _ (Sum.inl x)
⊕-η e i _ (Sum.inr x) = e _ (Sum.inr x)

_,⊕p_ : A ⊢ B → C ⊢ D → A ⊕ C ⊢ B ⊕ D
e ,⊕p f = ⊕-elim (inl ∘⊢ e) (inr ∘⊢ f)

infixr 20 _,⊕p_

⊕-swap : A ⊕ B ⊢ B ⊕ A
⊕-swap = ⊕-elim inr inl

module _ {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} where
  ⊕-swap-invol : ⊕-swap ∘⊢ ⊕-swap {A = A} {B = B} ≡ id⊢
  ⊕-swap-invol = ⊕≡ _ _ refl refl

module _ {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  {C : TheoryTy ℓC s} {D : TheoryTy ℓD s}
  (A≅B : A ≅ B) (C≅D : C ≅ D) where
  private
    the-fun : A ⊕ C ⊢ B ⊕ D
    the-fun = A≅B .fun ,⊕p C≅D .fun

    the-inv : B ⊕ D ⊢ A ⊕ C
    the-inv = A≅B .inv ,⊕p C≅D .inv

    the-sec : the-fun ∘⊢ the-inv ≡ id⊢
    the-sec = ⊕≡ _ _ (cong (inl ∘⊢_) (A≅B .sec)) (cong (inr ∘⊢_) (C≅D .sec))

    the-ret : the-inv ∘⊢ the-fun ≡ id⊢
    the-ret = ⊕≡ _ _ (cong (inl ∘⊢_) (A≅B .ret)) (cong (inr ∘⊢_) (C≅D .ret))

  ⊕≅ : (A ⊕ C) ≅ (B ⊕ D)
  ⊕≅ .fun = the-fun
  ⊕≅ .inv = the-inv
  ⊕≅ .sec = the-sec
  ⊕≅ .ret = the-ret

module _ {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} where
  ⊕-swap≅ : (A ⊕ B) ≅ (B ⊕ A)
  ⊕-swap≅ .fun = ⊕-swap
  ⊕-swap≅ .inv = ⊕-swap
  ⊕-swap≅ .sec = ⊕-swap-invol
  ⊕-swap≅ .ret = ⊕-swap-invol

module _ {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {C : TheoryTy ℓC s} where
  ⊕-assoc : (A ⊕ B) ⊕ C ⊢ A ⊕ (B ⊕ C)
  ⊕-assoc = ⊕-elim (⊕-elim inl (inr ∘⊢ inl)) (inr ∘⊢ inr)

  ⊕-assoc⁻ : A ⊕ (B ⊕ C) ⊢ (A ⊕ B) ⊕ C
  ⊕-assoc⁻ = ⊕-elim (inl ∘⊢ inl) (⊕-elim (inl ∘⊢ inr) inr)

  private
    the-sec : ⊕-assoc ∘⊢ ⊕-assoc⁻ ≡ id⊢
    the-sec = ⊕≡ _ _ refl (⊕≡ _ _ refl refl)

    the-ret : ⊕-assoc⁻ ∘⊢ ⊕-assoc ≡ id⊢
    the-ret = ⊕≡ _ _ (⊕≡ _ _ refl refl) refl

  ⊕-assoc≅ : ((A ⊕ B) ⊕ C) ≅ (A ⊕ (B ⊕ C))
  ⊕-assoc≅ .fun = ⊕-assoc
  ⊕-assoc≅ .inv = ⊕-assoc⁻
  ⊕-assoc≅ .sec = the-sec
  ⊕-assoc≅ .ret = the-ret
