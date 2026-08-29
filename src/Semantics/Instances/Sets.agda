{-# OPTIONS --lossy-unification #-}
{- The "just sets" model.

   Grammars are interpreted as plain sets and terms as plain functions:
   a grammar denotes its set of parse trees, with the string it parses
   forgotten. Concretely

     A ⊗ B   ↦  A × B          ε      ↦  Unit
     ⊕ᴰ      ↦  Σ              &ᴰ     ↦  Π
     A ⊸ B   ↦  A → B          B ⟜ A  ↦  A → B
     ＂ c ＂  ↦  Unit

   so every character contributes a single featureless token. Under
   this reading `char ≃ Gen` and `char * ≃ List Gen`, i.e. the type of
   strings reappears as the set of parse trees of `char *` — but it is
   now an ordinary Agda type, and terms of the DSL elaborate to
   ordinary Agda functions.

   Every universal property here holds by `refl` in both directions, so
   all of them are given by `strictContrFibers`.
-}
module Semantics.Instances.Sets where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv.Base using (strictContrFibers; equiv-proof)

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Morphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Limits.IndexedProduct.Base

open import Semantics.Model
open import Semantics.Structure.Biclosed
open import Semantics.Structure.IndexedCoproduct

open UniversalElement

module _ (ℓ : Level) where
  open MonoidalCategory
module _ (ℓ : Level) where
  open MonoidalCategory
  open MonoidalStr
  open TensorStr
  open Category
  open Functor
  open NatTrans
  open NatIso
  open isIso

  -- The structure maps, named so that the copattern definitions below
  -- have no argument patterns (which otherwise trips the termination
  -- checker on the nested record).
  private
    ⊗ob : hSet ℓ → hSet ℓ → hSet ℓ
    ⊗ob A B = (⟨ A ⟩ × ⟨ B ⟩) , isSet× (A .snd) (B .snd)

    ⊗hom : {A B A' B' : hSet ℓ}
         → (⟨ A ⟩ → ⟨ A' ⟩) → (⟨ B ⟩ → ⟨ B' ⟩)
         → ⟨ ⊗ob A B ⟩ → ⟨ ⊗ob A' B' ⟩
    ⊗hom f g x = f (x .fst) , g (x .snd)

    𝟙 : hSet ℓ
    𝟙 = Unit* , isSetUnit*

    assoc→ : {A B D : hSet ℓ}
           → ⟨ ⊗ob A (⊗ob B D) ⟩ → ⟨ ⊗ob (⊗ob A B) D ⟩
    assoc→ x = (x .fst , x .snd .fst) , x .snd .snd

    assoc← : {A B D : hSet ℓ}
           → ⟨ ⊗ob (⊗ob A B) D ⟩ → ⟨ ⊗ob A (⊗ob B D) ⟩
    assoc← x = x .fst .fst , (x .fst .snd , x .snd)

    lunit→ : {A : hSet ℓ} → ⟨ ⊗ob 𝟙 A ⟩ → ⟨ A ⟩
    lunit→ x = x .snd

    lunit← : {A : hSet ℓ} → ⟨ A ⟩ → ⟨ ⊗ob 𝟙 A ⟩
    lunit← a = tt* , a

    runit→ : {A : hSet ℓ} → ⟨ ⊗ob A 𝟙 ⟩ → ⟨ A ⟩
    runit→ x = x .fst

    runit← : {A : hSet ℓ} → ⟨ A ⟩ → ⟨ ⊗ob A 𝟙 ⟩
    runit← a = a , tt*

  ----------------------------------------------------------------
  -- Sets are cartesian monoidal.
  ----------------------------------------------------------------
  -- Given as a record expression rather than by copatterns: the α/η/ρ
  -- coherence fields have types mentioning the sibling fields, and with
  -- `refl` bodies that reads to the termination checker as a recursive
  -- call on the definition being made.
  SETMC : MonoidalCategory (ℓ-suc ℓ) ℓ
  SETMC = record
    { C = SET ℓ
    ; monstr = record
      { tenstr = record
        { ─⊗─ = record
          { F-ob = λ AB → ⊗ob (AB .fst) (AB .snd)
          ; F-hom = λ fg → ⊗hom (fg .fst) (fg .snd)
          ; F-id = refl
          ; F-seq = λ _ _ → refl
          }
        ; unit = 𝟙
        }
      ; α = record
        { trans = record { N-ob = λ _ → assoc→ ; N-hom = λ _ → refl }
        ; nIso = λ _ → record { inv = assoc← ; sec = refl ; ret = refl }
        }
      ; η = record
        { trans = record { N-ob = λ _ → lunit→ ; N-hom = λ _ → refl }
        ; nIso = λ _ → record { inv = lunit← ; sec = refl ; ret = refl }
        }
      ; ρ = record
        { trans = record { N-ob = λ _ → runit→ ; N-hom = λ _ → refl }
        ; nIso = λ _ → record { inv = runit← ; sec = refl ; ret = refl }
        }
      ; pentagon = λ _ _ _ _ → refl
      ; triangle = λ _ _ → refl
      }
    }
  ----------------------------------------------------------------
  -- Both closures are the function set (the tensor is symmetric).
  ----------------------------------------------------------------
  ⊸SET : (B D : hSet ℓ) → ⊸At SETMC B D
  ⊸SET B D .vertex = (⟨ B ⟩ → ⟨ D ⟩) , isSet→ (D .snd)
  ⊸SET B D .element (f , b) = f b
  ⊸SET B D .universal A .equiv-proof =
    strictContrFibers (λ g a b → g (a , b))

  ⟜SET : (A D : hSet ℓ) → ⟜At SETMC A D
  ⟜SET A D .vertex = (⟨ A ⟩ → ⟨ D ⟩) , isSet→ (D .snd)
  ⟜SET A D .element (a , f) = f a
  ⟜SET A D .universal B .equiv-proof =
    strictContrFibers (λ g b a → g (a , b))

  ----------------------------------------------------------------
  -- Indexed products and coproducts are Π and Σ.
  ----------------------------------------------------------------
  ΠSET : (X : hSet ℓ) (A : ⟨ X ⟩ → hSet ℓ) → ΠTy (SET ℓ) A
  ΠSET X A .vertex =
    ((x : ⟨ X ⟩) → ⟨ A x ⟩) , isSetΠ (λ x → A x .snd)
  ΠSET X A .element x f = f x
  ΠSET X A .universal Γ .equiv-proof =
    strictContrFibers (λ h γ x → h x γ)

  ΣSET : (X : hSet ℓ) (A : ⟨ X ⟩ → hSet ℓ) → ΣTy (SET ℓ) A
  ΣSET X A .vertex =
    (Σ[ x ∈ ⟨ X ⟩ ] ⟨ A x ⟩) , isSetΣ (X .snd) (λ x → A x .snd)
  ΣSET X A .element x a = x , a
  ΣSET X A .universal Γ .equiv-proof =
    strictContrFibers (λ h (x , a) → h x a)

  ----------------------------------------------------------------
  Sets : Model (ℓ-suc ℓ) ℓ ℓ
  Sets .Model.MC = SETMC
  Sets .Model.biclosed .Biclosed.⊸ues = ⊸SET
  Sets .Model.biclosed .Biclosed.⟜ues = ⟜SET
  Sets .Model.Πs = ΠSET
  Sets .Model.Σs = ΣSET

  SetsOn : (Gen : hSet ℓ) → GrammarModel (ℓ-suc ℓ) ℓ ℓ Gen
  SetsOn Gen .GrammarModel.model = Sets
  SetsOn Gen .GrammarModel.⟦lit⟧ _ = Unit* , isSetUnit*
