-- Codes for strictly positive functors
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Code.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Foundations.More

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Lift.Base σeq V vs 𝒫
open import Theory.Type.Sum.Base σeq V vs 𝒫
open import Theory.Type.Product.Base σeq V vs 𝒫
open import Theory.Type.Product.Binary.Base σeq V vs 𝒫
open import Theory.Type.Operation.Base σeq V vs 𝒫

private variable ℓB ℓC ℓD : Level

ℓF : Level → Level
ℓF ℓA = ℓS ⊔ℓ ℓ ⊔ℓ (ℓ-suc ℓA) ⊔ℓ ℓM

data Functor (ℓA : Level) {ℓX} (X : Type ℓX) (xs : X → S)
  : S → Type (ℓ-suc ℓX ⊔ℓ ℓF ℓA) where
  k : {s : S} → TheoryTy ℓA s → Functor ℓA X xs s
  Var : (x : X) → Functor ℓA X xs (xs x)
  ⊕e &e : {s : S} (Y : Type ℓX) → (Y → Functor ℓA X xs s) → Functor ℓA X xs s
  _&e2_ : {s : S} → Functor ℓA X xs s → Functor ℓA X xs s → Functor ℓA X xs s
  ⊗e : (o : σ .ops) → interpIn o (Functor ℓA X xs)
     → Functor ℓA X xs (σ .resultSort o)

module _ {ℓA ℓX} {X : Type ℓX} {xs : X → S} where
  ⟦_⟧TheoryTy : ∀ {s} → Functor ℓA X xs s → ((x : X) → TheoryTy ℓB (xs x))
    → TheoryTy (ℓB ⊔ℓ ℓF ℓA ⊔ℓ ℓX) s
  ⟦_⟧TheoryTy {ℓB = ℓB} (k B) A = LiftTheoryTy (ℓB ⊔ℓ ℓF ℓA ⊔ℓ ℓX) B
  ⟦ Var x ⟧TheoryTy A = LiftTheoryTy (ℓF ℓA ⊔ℓ ℓX) (A x)
  ⟦ ⊕e Y F ⟧TheoryTy A = ⊕[ y ∈ Y ] ⟦ F y ⟧TheoryTy A
  ⟦ &e Y F ⟧TheoryTy A = &[ y ∈ Y ] ⟦ F y ⟧TheoryTy A
  ⟦ F &e2 F' ⟧TheoryTy A = ⟦ F ⟧TheoryTy A & ⟦ F' ⟧TheoryTy A
  ⟦ ⊗e o F ⟧TheoryTy A = ⊗ᵘ[ o ] λ (a : arities σ o) → ⟦ F a ⟧TheoryTy A

  map : ∀ {s} (F : Functor ℓA X xs s)
    {A : (x : X) → TheoryTy ℓB (xs x)}
    {B : (x : X) → TheoryTy ℓC (xs x)}
    → (∀ x → A x ⊢ B x)
    → ⟦ F ⟧TheoryTy A ⊢ ⟦ F ⟧TheoryTy B
  map (k K) f = liftTy ∘⊢ lowerTy
  map (Var x) f = liftTy ∘⊢ f x ∘⊢ lowerTy
  map (⊕e Y F) f = ⊕ᴰ-elim λ y → σ⊕ y ∘⊢ map (F y) f
  map (&e Y F) f = &ᴰ-intro λ y → map (F y) f ∘⊢ π y
  map (F &e2 F') f = map F f ,&p map F' f
  map (⊗e o F) f = ⊗map o λ a → map (F a) f

  map-id : ∀ {s} (F : Functor ℓA X xs s) {A : (x : X) → TheoryTy ℓB (xs x)}
    → map F (λ x → id⊢ {A = A x}) ≡ id⊢
  map-id (k K) i = id⊢
  map-id (Var x) i = id⊢
  map-id (⊕e Y F) i = ⊕ᴰ-elim λ y → σ⊕ y ∘⊢ map-id (F y) i
  map-id (&e Y F) i = &ᴰ-intro λ y → map-id (F y) i ∘⊢ π y
  map-id (F &e2 F') i = map-id F i ,&p map-id F' i
  map-id (⊗e o F) i = ⊗map o λ a → map-id (F a) i

  map-∘ : ∀ {s}
    {A : (x : X) → TheoryTy ℓB (xs x)}
    {B : (x : X) → TheoryTy ℓC (xs x)}
    {C : (x : X) → TheoryTy ℓD (xs x)}
    (F : Functor ℓA X xs s)
    (f : ∀ x → B x ⊢ C x) (f' : ∀ x → A x ⊢ B x)
    → map F (λ x → f x ∘⊢ f' x) ≡ map F f ∘⊢ map F f'
  map-∘ (k K) f f' i = liftTy ∘⊢ lowerTy
  map-∘ (Var x) f f' i = liftTy ∘⊢ f x ∘⊢ f' x ∘⊢ lowerTy
  map-∘ (⊕e Y F) f f' i = ⊕ᴰ-elim λ y → σ⊕ y ∘⊢ map-∘ (F y) f f' i
  map-∘ (&e Y F) f f' i = &ᴰ-intro λ y → map-∘ (F y) f f' i ∘⊢ π y
  map-∘ (F &e2 F') f f' i = map-∘ F f f' i ,&p map-∘ F' f f' i
  map-∘ (⊗e o F) f f' i = ⊗map o λ a → map-∘ (F a) f f' i

  map-inv : ∀ {s} (F : Functor ℓA X xs s)
    {A : (x : X) → TheoryTy ℓB (xs x)}
    {B : (x : X) → TheoryTy ℓC (xs x)}
    (f : ∀ x → A x ⊢ B x) (g : ∀ x → B x ⊢ A x)
    → (∀ x → f x ∘⊢ g x ≡ id⊢)
    → map F f ∘⊢ map F g ≡ id⊢
  map-inv F f g p =
    sym (map-∘ F f g) ∙ cong (map F) (funExt p) ∙ map-id F
