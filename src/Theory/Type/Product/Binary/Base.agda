open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Product.Binary.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Sigma
open import Cubical.WildCat.LocallySmall.Base

open import Theory.Base σeq V vs 𝒫

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

_&_ : ∀ {s} → TheoryTy ℓA s → TheoryTy ℓB s → TheoryTy (ℓ-max ℓA ℓB) s
(A & B) m = A m × B m

infixr 27 _&_

&-intro : A ⊢ B → A ⊢ C → A ⊢ B & C
&-intro e e' _ p = e _ p , e' _ p

_,&_ = &-intro
infixr 20 _,&_

π₁ : A & B ⊢ A
π₁ _ p = p .fst

π₂ : A & B ⊢ B
π₂ _ p = p .snd

&-β₁ : (e₁ : A ⊢ B) (e₂ : A ⊢ C) → π₁ ∘⊢ (e₁ ,& e₂) ≡ e₁
&-β₁ e₁ e₂ = refl

&-β₂ : (e₁ : A ⊢ B) (e₂ : A ⊢ C) → π₂ ∘⊢ (e₁ ,& e₂) ≡ e₂
&-β₂ e₁ e₂ = refl

&-η : (e : A ⊢ B & C) → (π₁ ∘⊢ e) ,& (π₂ ∘⊢ e) ≡ e
&-η e = refl

&≡ : (f f' : A ⊢ B & C)
  → π₁ ∘⊢ f ≡ π₁ ∘⊢ f' → π₂ ∘⊢ f ≡ π₂ ∘⊢ f'
  → f ≡ f'
&≡ f f' π₁≡ π₂≡ = funExt λ m → funExt λ p i → π₁≡ i m p , π₂≡ i m p

&-η' : (e e' : A ⊢ B & C)
  → π₁ ∘⊢ e ≡ π₁ ∘⊢ e' → π₂ ∘⊢ e ≡ π₂ ∘⊢ e'
  → e ≡ e'
&-η' e e' p₁ p₂ = sym (&-η e) ∙ cong₂ &-intro p₁ p₂ ∙ &-η e'

&par : A ⊢ B → C ⊢ D → A & C ⊢ B & D
&par f f' = (f ∘⊢ π₁) ,& (f' ∘⊢ π₂)

_,&p_ = &par
infixr 20 _,&p_

id&_ : B ⊢ C → A & B ⊢ A & C
id& f = π₁ ,& (f ∘⊢ π₂)

&-swap : A & B ⊢ B & A
&-swap = π₂ ,& π₁

&-Δ : A ⊢ A & A
&-Δ = id⊢ ,& id⊢

&-swap-invol : &-swap ∘⊢ &-swap {A = A} {B = B} ≡ id⊢
&-swap-invol = refl

&-assoc : A & (B & C) ⊢ (A & B) & C
&-assoc = (π₁ ,& (π₁ ∘⊢ π₂)) ,& (π₂ ∘⊢ π₂)

&-assoc⁻ : (A & B) & C ⊢ A & (B & C)
&-assoc⁻ = (π₁ ∘⊢ π₁) ,& ((π₂ ∘⊢ π₁) ,& π₂)

module _ {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  {C : TheoryTy ℓC s} {D : TheoryTy ℓD s}
  (A≅B : A ≅ B) (C≅D : C ≅ D) where
  private
    the-fun : A & C ⊢ B & D
    the-fun = A≅B .fun ,&p C≅D .fun

    the-inv : B & D ⊢ A & C
    the-inv = A≅B .inv ,&p C≅D .inv

    the-sec : the-fun ∘⊢ the-inv ≡ id⊢
    the-sec = &≡ _ _ (cong (_∘⊢ π₁) (A≅B .sec)) (cong (_∘⊢ π₂) (C≅D .sec))

    the-ret : the-inv ∘⊢ the-fun ≡ id⊢
    the-ret = &≡ _ _ (cong (_∘⊢ π₁) (A≅B .ret)) (cong (_∘⊢ π₂) (C≅D .ret))

  &≅ : (A & C) ≅ (B & D)
  &≅ .fun = the-fun
  &≅ .inv = the-inv
  &≅ .sec = the-sec
  &≅ .ret = the-ret

module _ {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} where
  &-swap≅ : (A & B) ≅ (B & A)
  &-swap≅ .fun = &-swap
  &-swap≅ .inv = &-swap
  &-swap≅ .sec = &-swap-invol
  &-swap≅ .ret = &-swap-invol
