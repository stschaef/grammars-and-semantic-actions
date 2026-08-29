{-# OPTIONS --lossy-unification #-}
{- The recursor: interpreting the syntax in any model.

   The free model is initial, so every `GrammarModel` with the same
   generators receives a structure-preserving map from it. Unlike the
   eliminator, this needs no displayed machinery: each path constructor
   is discharged by the target model's own law, and a plain
   `UniversalElement`'s β/η carry none of the `reind` that the
   *displayed* representable's action inserts.

   This is what the gluing arguments need in order to even state a
   logical relation: the two interpretations being related.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Semantics.Model

module Semantics.Free.Recursor {ℓ ℓ' ℓX} {Gen : hSet ℓX}
  (M : GrammarModel ℓ ℓ' ℓX Gen) where

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Morphism

open import Semantics.Notation M
open import Semantics.Free.Syntax Gen

open NatTrans
open NatIso
open isIso
open Functor

recOb : Ty → Grammar
recOb (↑ g) = literal g
recOb εT = ε
recOb (A ⊗T B) = recOb A ⊗ recOb B
recOb (A ⊸T B) = recOb A ⊸ recOb B
recOb (A ⟜T B) = recOb A ⟜ recOb B
recOb (⊕T X A) = ⊕ᴰ {X = X} (λ x → recOb (A x))
recOb (&T X A) = &ᴰ {X = X} (λ x → recOb (A x))

recHom : ∀ {A B} → Exp A B → recOb A ⊢ recOb B
-- category
recHom idE = id
recHom (f ⋆E g) = recHom g ∘g recHom f
recHom (⋆IdLE f i) = ⋆IdL (recHom f) i
recHom (⋆IdRE f i) = ⋆IdR (recHom f) i
recHom (⋆AssocE f g h i) = ⋆Assoc (recHom f) (recHom g) (recHom h) i
recHom (isSetExp f g p q i j) =
  isSetHom (recHom f) (recHom g) (λ i → recHom (p i)) (λ i → recHom (q i)) i j
-- tensor
recHom (f ⊗E g) = recHom f ,⊗ recHom g
recHom (⊗E-id i) = ─⊗─ .F-id i
recHom (⊗E-seq f g f' g' i) =
  ─⊗─ .F-seq (recHom f , recHom f') (recHom g , recHom g') i
-- associator
recHom αE = α⟨ _ , _ , _ ⟩
recHom αE⁻ = α⁻¹⟨ _ , _ , _ ⟩
recHom (α-sec i) = α .nIso _ .sec i
recHom (α-ret i) = α .nIso _ .ret i
recHom (α-nat f g h i) =
  α .trans .N-hom (recHom f , recHom g , recHom h) i
-- left unitor
recHom ηE = η⟨ _ ⟩
recHom ηE⁻ = η⁻¹⟨ _ ⟩
recHom (η-sec i) = η .nIso _ .sec i
recHom (η-ret i) = η .nIso _ .ret i
recHom (η-nat f i) = η .trans .N-hom (recHom f) i
-- right unitor
recHom ρE = ρ⟨ _ ⟩
recHom ρE⁻ = ρ⁻¹⟨ _ ⟩
recHom (ρ-sec i) = ρ .nIso _ .sec i
recHom (ρ-ret i) = ρ .nIso _ .ret i
recHom (ρ-nat f i) = ρ .trans .N-hom (recHom f) i
-- coherence
recHom (pentagonE i) = pentagon _ _ _ _ i
recHom (triangleE i) = triangle _ _ i
-- ⊸
recHom ⊸appE = ⊸-app
recHom (⊸lamE f) = ⊸-intro (recHom f)
recHom (⊸βE f i) = ⊸-β {f = recHom f} i
recHom (⊸ηE g i) = ⊸-η {g = recHom g} i
-- ⟜
recHom ⟜appE = ⟜-app
recHom (⟜lamE f) = ⟜-intro (recHom f)
recHom (⟜βE f i) = ⟜-β {f = recHom f} i
recHom (⟜ηE g i) = ⟜-η {g = recHom g} i
-- indexed coproducts
recHom (σE x) = σ x
recHom (⊕elimE f) = ⊕ᴰ-elim (λ x → recHom (f x))
recHom (⊕βE X A f x i) =
  ⊕ᴰ-β {X = X} {A = λ y → recOb (A y)} (λ y → recHom (f y)) x i
recHom (⊕ηE X A g i) =
  ⊕ᴰ-η {X = X} {A = λ y → recOb (A y)} (recHom g) i
-- indexed products
recHom (πE x) = π x
recHom (&introE f) = &ᴰ-intro (λ x → recHom (f x))
recHom (&βE X A f x i) =
  &ᴰ-β {X = X} {A = λ y → recOb (A y)} (λ y → recHom (f y)) x i
recHom (&ηE X A g i) =
  &ᴰ-η {X = X} {A = λ y → recOb (A y)} (recHom g) i
