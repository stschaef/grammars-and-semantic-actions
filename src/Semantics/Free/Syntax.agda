{-# OPTIONS --lossy-unification #-}
{- The free model: syntax.

   Following ccl's `Free/CartesianCategory/Base`, objects are a plain
   inductive type and morphisms a quotient inductive type indexed by
   them — objects never mention morphisms, so there is no
   induction-induction.

   Going infinitary, `⊕T` and `&T` quantify over an arbitrary `hSet ℓ`.
   That is strictly positive, so Agda accepts it; it just places `Ty`
   (and hence `Exp`) at `ℓ-suc ℓ`. The free model is therefore a
   `Model (ℓ-suc ℓ) (ℓ-suc ℓ) ℓ` — one universe up on objects and
   homs, but still indexed by `hSet ℓ`, so it is initial among models
   whose index level is ℓ. No local smallness is needed.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Semantics.Free.Syntax {ℓ} (Gen : hSet ℓ) where

------------------------------------------------------------------------
-- Objects
------------------------------------------------------------------------

data Ty : Type (ℓ-suc ℓ) where
  ↑_ : ⟨ Gen ⟩ → Ty
  εT : Ty
  _⊗T_ : Ty → Ty → Ty
  _⊸T_ : Ty → Ty → Ty
  _⟜T_ : Ty → Ty → Ty
  ⊕T : (X : hSet ℓ) → (⟨ X ⟩ → Ty) → Ty
  &T : (X : hSet ℓ) → (⟨ X ⟩ → Ty) → Ty

infixr 25 _⊗T_
infixr 2 _⊸T_
infixl 2 _⟜T_

------------------------------------------------------------------------
-- Morphisms
------------------------------------------------------------------------

data Exp : Ty → Ty → Type (ℓ-suc ℓ) where
  -- category
  idE : ∀ {A} → Exp A A
  _⋆E_ : ∀ {A B D} → Exp A B → Exp B D → Exp A D
  ⋆IdLE : ∀ {A B} (f : Exp A B) → idE ⋆E f ≡ f
  ⋆IdRE : ∀ {A B} (f : Exp A B) → f ⋆E idE ≡ f
  ⋆AssocE : ∀ {A B D E} (f : Exp A B) (g : Exp B D) (h : Exp D E)
          → (f ⋆E g) ⋆E h ≡ f ⋆E (g ⋆E h)
  isSetExp : ∀ {A B} → isSet (Exp A B)

  -- ⊗ is a bifunctor
  _⊗E_ : ∀ {A B D E} → Exp A B → Exp D E → Exp (A ⊗T D) (B ⊗T E)
  ⊗E-id : ∀ {A B} → idE {A} ⊗E idE {B} ≡ idE
  ⊗E-seq : ∀ {A B D A' B' D'}
    (f : Exp A B) (g : Exp B D) (f' : Exp A' B') (g' : Exp B' D')
    → (f ⋆E g) ⊗E (f' ⋆E g') ≡ (f ⊗E f') ⋆E (g ⊗E g')

  -- associator
  αE : ∀ {A B D} → Exp (A ⊗T (B ⊗T D)) ((A ⊗T B) ⊗T D)
  αE⁻ : ∀ {A B D} → Exp ((A ⊗T B) ⊗T D) (A ⊗T (B ⊗T D))
  α-sec : ∀ {A B D} → αE⁻ {A} {B} {D} ⋆E αE ≡ idE
  α-ret : ∀ {A B D} → αE {A} {B} {D} ⋆E αE⁻ ≡ idE
  α-nat : ∀ {A B D A' B' D'}
    (f : Exp A A') (g : Exp B B') (h : Exp D D')
    → (f ⊗E (g ⊗E h)) ⋆E αE ≡ αE ⋆E ((f ⊗E g) ⊗E h)

  -- left unitor
  ηE : ∀ {A} → Exp (εT ⊗T A) A
  ηE⁻ : ∀ {A} → Exp A (εT ⊗T A)
  η-sec : ∀ {A} → ηE⁻ {A} ⋆E ηE ≡ idE
  η-ret : ∀ {A} → ηE {A} ⋆E ηE⁻ ≡ idE
  η-nat : ∀ {A B} (f : Exp A B) → (idE ⊗E f) ⋆E ηE ≡ ηE ⋆E f

  -- right unitor
  ρE : ∀ {A} → Exp (A ⊗T εT) A
  ρE⁻ : ∀ {A} → Exp A (A ⊗T εT)
  ρ-sec : ∀ {A} → ρE⁻ {A} ⋆E ρE ≡ idE
  ρ-ret : ∀ {A} → ρE {A} ⋆E ρE⁻ ≡ idE
  ρ-nat : ∀ {A B} (f : Exp A B) → (f ⊗E idE) ⋆E ρE ≡ ρE ⋆E f

  -- coherence
  pentagonE : ∀ {W X Y Z}
    → (idE {W} ⊗E αE {X} {Y} {Z}) ⋆E (αE ⋆E (αE ⊗E idE))
    ≡ αE ⋆E αE
  triangleE : ∀ {X Y}
    → αE {X} {εT} {Y} ⋆E (ρE ⊗E idE) ≡ idE ⊗E ηE

  -- ⊸ : right adjoint to (- ⊗ B)
  ⊸appE : ∀ {B D} → Exp ((B ⊸T D) ⊗T B) D
  ⊸lamE : ∀ {A B D} → Exp (A ⊗T B) D → Exp A (B ⊸T D)
  ⊸βE : ∀ {A B D} (f : Exp (A ⊗T B) D)
      → (⊸lamE f ⊗E idE) ⋆E ⊸appE ≡ f
  ⊸ηE : ∀ {A B D} (g : Exp A (B ⊸T D))
      → g ≡ ⊸lamE ((g ⊗E idE) ⋆E ⊸appE)

  -- ⟜ : right adjoint to (A ⊗ -)
  ⟜appE : ∀ {A D} → Exp (A ⊗T (D ⟜T A)) D
  ⟜lamE : ∀ {A B D} → Exp (A ⊗T B) D → Exp B (D ⟜T A)
  ⟜βE : ∀ {A B D} (f : Exp (A ⊗T B) D)
      → (idE ⊗E ⟜lamE f) ⋆E ⟜appE ≡ f
  ⟜ηE : ∀ {A B D} (g : Exp B (D ⟜T A))
      → g ≡ ⟜lamE ((idE ⊗E g) ⋆E ⟜appE)

  -- set-indexed coproducts
  σE : ∀ {X A} (x : ⟨ X ⟩) → Exp (A x) (⊕T X A)
  ⊕elimE : ∀ {X A B} → (∀ x → Exp (A x) B) → Exp (⊕T X A) B
  ⊕βE : ∀ {B} (X : hSet ℓ) (A : ⟨ X ⟩ → Ty)
      → (f : ∀ x → Exp (A x) B) (x : ⟨ X ⟩)
      → σE x ⋆E ⊕elimE f ≡ f x
  ⊕ηE : ∀ {B} (X : hSet ℓ) (A : ⟨ X ⟩ → Ty) (g : Exp (⊕T X A) B)
      → g ≡ ⊕elimE (λ x → σE x ⋆E g)

  -- set-indexed products
  πE : ∀ {X A} (x : ⟨ X ⟩) → Exp (&T X A) (A x)
  &introE : ∀ {X A B} → (∀ x → Exp B (A x)) → Exp B (&T X A)
  &βE : ∀ {B} (X : hSet ℓ) (A : ⟨ X ⟩ → Ty)
      → (f : ∀ x → Exp B (A x)) (x : ⟨ X ⟩)
      → &introE f ⋆E πE x ≡ f x
  &ηE : ∀ {B} (X : hSet ℓ) (A : ⟨ X ⟩ → Ty) (g : Exp B (&T X A))
      → g ≡ &introE (λ x → g ⋆E πE x)

infixr 9 _⋆E_
infixr 25 _⊗E_
