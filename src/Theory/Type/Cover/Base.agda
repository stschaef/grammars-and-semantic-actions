open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Cover.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Equality as Eq

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Top.Base σeq V vs 𝒫
open import Theory.Type.Bottom.Base σeq V vs 𝒫
open import Theory.Type.Sum.Base σeq V vs 𝒫
open import Theory.Type.Product.Binary.Base σeq V vs 𝒫
open import Theory.Type.Lift.Base σeq V vs 𝒫
open import Theory.Type.Monad.Maybe σeq V vs 𝒫

private variable ℓA ℓB ℓY : Level

Point : ∀ {s} → TheoryTy ℓA s → Type (ℓ-max ℓM ℓA)
Point A = ⊤Ty ⊢ A

Disjoint : ∀ {s} {Y : Type ℓY} → (Y → TheoryTy ℓA s) → Type _
Disjoint {Y = Y} A = ∀ (y y' : Y) → (y Eq.≡ y' → ⊥) → A y & A y' ⊢ ⊥Ty

Total : ∀ {s} {Y : Type ℓY} → (Y → TheoryTy ℓA s) → Type _
Total {Y = Y} A = Point (⊕[ y ∈ Y ] A y)

record Cover {s} (Y : Type ℓY) (A : Y → TheoryTy ℓA s)
  : Type (ℓ-max ℓY (ℓ-max ℓM ℓA)) where
  field
    disjoint : Disjoint A
    total : Total A

open Cover public

module _ {s} {Y : Type ℓY} {A : Y → TheoryTy ℓA s} {B : TheoryTy ℓB s} where
  cover-elim : Cover Y A → (∀ y → A y ⊢ B) → Point B
  cover-elim c f = ⊕ᴰ-elim f ∘⊢ c .total

-- A classifier reading the index off any inhabitant makes the family
-- disjoint: one point cannot classify to two indices.
clsDisjoint : ∀ {s} {Y : Type ℓY} {A : Y → TheoryTy ℓA s}
  (cls : ↓M s → Y) → (∀ y m → A y m → cls m ≡ y) → Disjoint A
clsDisjoint cls sound y y' ne m (p , p') =
  Empty.rec (ne (Eq.pathToEq (sym (sound y m p) ∙ sound y' m p')))

trivialCover : ∀ {s} → Cover Unit (λ _ → LiftTheoryTy ℓA (⊤Ty {s = s}))
trivialCover .total = σ⊕ tt ∘⊢ liftTy
trivialCover .disjoint y y' ne = Empty.rec (ne Eq.refl)

record Covering (s : S) (ℓY ℓA : Level)
  : Type (ℓ-max (ℓ-suc ℓY) (ℓ-max ℓM (ℓ-suc ℓA))) where
  field
    Idx  : Type ℓY
    Part : Idx → TheoryTy ℓA s
    cov  : Cover Idx Part

open Covering public

ofCover : ∀ {s} {Y : Type ℓY} {A : Y → TheoryTy ℓA s}
  → Cover Y A → Covering s ℓY ℓA
ofCover {Y = Y} c .Idx = Y
ofCover {A = A} c .Part = A
ofCover c .cov = c

record Cases {s : S} (ℓY ℓA : Level) {ℓR : Level}
  (A : TheoryTy ℓA s → Type ℓR)
  : Type (ℓ-max (ℓ-suc ℓY) (ℓ-max ℓM (ℓ-max (ℓ-suc ℓA) ℓR))) where
  field
    cover : Covering s ℓY ℓA
    act : (i : cover .Idx) → A (cover .Part i)

open Cases public
