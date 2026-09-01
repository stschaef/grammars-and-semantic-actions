-- An interface to guarded recursion
{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Guarded.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Top.Base σeq V vs 𝒫
open import Theory.Type.Inductive.Base σeq V vs 𝒫

private variable ℓA ℓB ℓR ℓX : Level

-- where a guarded recursion is at: an index and an input
Pt : {X : Type ℓX} (xs : X → S) → Type (ℓ-max ℓX ℓM)
Pt {X = X} xs = Σ[ x ∈ X ] ↓M (xs x)

module _ {X : Type ℓX} {xs : X → S} where

  -- Löb, with `▷` abstract
  record Löb (R : Pt xs → Pt xs → Type ℓR)
    (A : (x : X) → TheoryTy ℓA (xs x)) : Typeω where
    field
      ℓ▷ : Level
      ▷ : (x : X) → TheoryTy ℓ▷ (xs x)
      next : (∀ x → ⊤Ty ⊢ A x) → ∀ x → ⊤Ty ⊢ ▷ x
      app : ∀ {x m x' m'} → R (x' , m') (x , m) → ▷ x m → A x' m'
      löb : (∀ x → ▷ x ⊢ A x) → ∀ x → ⊤Ty ⊢ A x
      löb-unfold : (φ : ∀ x → ▷ x ⊢ A x)
        → ∀ x → löb φ x ≡ φ x ∘⊢ next (löb φ) x
      löb-uniq : (φ : ∀ x → ▷ x ⊢ A x) (t : ∀ x → ⊤Ty ⊢ A x)
        → (∀ x → t x ≡ φ x ∘⊢ next t x) → t ≡ löb φ
      -- the β-rule: what `next` promised is what `app` delivers
      app-next : (t : ∀ x → ⊤Ty ⊢ A x)
        → ∀ {x m x' m'} (r : R (x' , m') (x , m))
        → app r (next t x m tt) ≡ t x' m' tt

  -- Hylomorphisms, uniquely: a coalgebra and an algebra give the one map
  -- commuting with them.
  record Hylos (F : (x : X) → Functor ℓA X xs (xs x)) : Typeω where
    field
      hylo : {ℓB : Level} {A B : (x : X) → TheoryTy ℓB (xs x)}
        → (∀ x m → isSet (B x m))
        → (c : ∀ x → A x ⊢ ⟦ F x ⟧TheoryTy A)
        → (α : ∀ x → ⟦ F x ⟧TheoryTy B ⊢ B x)
        → ∀ x → A x ⊢ B x
      hylo-unfold : {ℓB : Level} {A B : (x : X) → TheoryTy ℓB (xs x)}
        (isSetB : ∀ x m → isSet (B x m))
        (c : ∀ x → A x ⊢ ⟦ F x ⟧TheoryTy A)
        (α : ∀ x → ⟦ F x ⟧TheoryTy B ⊢ B x)
        → ∀ x → hylo isSetB c α x
              ≡ α x ∘⊢ map (F x) (hylo isSetB c α) ∘⊢ c x

  module _ {F : (x : X) → Functor ℓA X xs (xs x)} (H : Hylos F) where
    open Hylos H public

    -- a coalgebra is one step of parsing; folding it into the initial
    -- algebra is the parse tree -- no modality in sight
    unfold : {A : (x : X) → TheoryTy (ℓ-max (ℓF ℓA) ℓX) (xs x)}
      → (∀ x m → isSet (μ F x m))
      → (∀ x → A x ⊢ ⟦ F x ⟧TheoryTy A)
      → ∀ x → A x ⊢ μ F x
    unfold isSetμF c = hylo isSetμF c λ x → roll

    -- The recursor, by guarded recursion rather than by matching on `roll`.
    fold : {A : (x : X) → TheoryTy (ℓ-max (ℓF ℓA) ℓX) (xs x)}
      → (∀ x m → isSet (A x m))
      → (∀ x → ⟦ F x ⟧TheoryTy A ⊢ A x)
      → ∀ x → μ F x ⊢ A x
    fold isSetA α = hylo isSetA (unroll F) α

    -- the β-law comes with it, rather than being a separate `refl`
    fold-unfold : {A : (x : X) → TheoryTy (ℓ-max (ℓF ℓA) ℓX) (xs x)}
      (isSetA : ∀ x m → isSet (A x m))
      (α : ∀ x → ⟦ F x ⟧TheoryTy A ⊢ A x)
      → ∀ x → fold isSetA α x
            ≡ α x ∘⊢ map (F x) (fold isSetA α) ∘⊢ unroll F x
    fold-unfold isSetA α = hylo-unfold isSetA (unroll F) α
