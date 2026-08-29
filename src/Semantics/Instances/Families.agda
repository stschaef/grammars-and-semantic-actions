{-# OPTIONS --lossy-unification #-}
{- The families-of-sets model.

   The original semantics — grammars are set-valued families over
   strings, terms are string-indexed functions — is one model of
   `Semantics.Model`. Every structure required by the model is
   witnessed by a definition that already exists in `Grammar.*`:

     monoidal      Term.Category.GRAMMAR
     biclosure     Grammar.LinearFunction (⊸-β/⊸-η, ⟜-β/⟜-η)
     &ᴰ            Grammar.Product        (π, &ᴰ-intro)
     ⊕ᴰ            Grammar.Sum            (σ, ⊕ᴰ-elim)

   Note how little is needed: in each case the β and η laws of the
   pointful definition hold by `refl`, so the universal property is
   immediate.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Instances.Families (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Categories.Category
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Limits.IndexedProduct.Base

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet hiding (⟨_⟩)
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.LinearFunction.Base Alphabet
open import Grammar.Product.Base Alphabet
open import Grammar.Product.Properties Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.Sum.Properties Alphabet
open import Grammar.Literal.Base Alphabet
open import Term.Base Alphabet
open import Term.Category Alphabet

open import Semantics.Model
open import Semantics.Structure.Biclosed
open import Semantics.Structure.IndexedCoproduct

open UniversalElement
open Iso

module _ (ℓ : Level) where
  private
    MC = GRAMMAR ℓ
    module MC = MonoidalCategory MC

  ----------------------------------------------------------------
  -- Set-indexed products are &ᴰ.
  ----------------------------------------------------------------
  ΠGrammar : (X : hSet ℓ) (A : ⟨ X ⟩ → MC.ob) → ΠTy MC.C A
  ΠGrammar X A .vertex =
    (&[ x ∈ ⟨ X ⟩ ] (A x .fst)) , isSetGrammar&ᴰ (λ x → A x .snd)
  ΠGrammar X A .element x = π x
  ΠGrammar X A .universal B =
    isoToIsEquiv (iso (λ f x → π x ∘g f) &ᴰ-intro (λ _ → refl) (λ _ → refl))

  ----------------------------------------------------------------
  -- Set-indexed coproducts are ⊕ᴰ. The index must be an h-set for
  -- the sum to stay set-valued.
  ----------------------------------------------------------------
  ΣGrammar : (X : hSet ℓ) (A : ⟨ X ⟩ → MC.ob) → ΣTy MC.C A
  ΣGrammar X A .vertex =
    (⊕[ x ∈ ⟨ X ⟩ ] (A x .fst)) , isSetGrammar⊕ᴰ (X .snd) (λ x → A x .snd)
  ΣGrammar X A .element x = σ x
  ΣGrammar X A .universal B =
    isoToIsEquiv (iso (λ f x → f ∘g σ x) ⊕ᴰ-elim (λ _ → refl) (λ _ → refl))

  ----------------------------------------------------------------
  -- The biclosure is ⊸ and ⟜.
  ----------------------------------------------------------------
  ⊸Grammar : (B D : MC.ob) → ⊸At MC B D
  ⊸Grammar B D .vertex = (B .fst ⊸ D .fst) , isSetGrammar⊸ (D .snd)
  ⊸Grammar B D .element = ⊸-app
  ⊸Grammar B D .universal A =
    isoToIsEquiv (iso ⊸-intro⁻ ⊸-intro ⊸-β ⊸-η)

  ⟜Grammar : (A D : MC.ob) → ⟜At MC A D
  ⟜Grammar A D .vertex = (D .fst ⟜ A .fst) , isSetGrammar⟜ (D .snd)
  ⟜Grammar A D .element = ⟜-app
  ⟜Grammar A D .universal B =
    isoToIsEquiv (iso ⟜-intro⁻ ⟜-intro ⟜-β (λ f → sym (⟜-η f)))

  ----------------------------------------------------------------
  Families : Model (ℓ-suc ℓ) ℓ ℓ
  Families .Model.MC = MC
  Families .Model.biclosed .Biclosed.⊸ues = ⊸Grammar
  Families .Model.biclosed .Biclosed.⟜ues = ⟜Grammar
  Families .Model.Πs = ΠGrammar
  Families .Model.Σs = ΣGrammar

  -- A families model for any choice of generators.
  FamiliesOn : (Gen : hSet ℓ) (lit : ⟨ Gen ⟩ → SetGrammar ℓ)
    → GrammarModel (ℓ-suc ℓ) ℓ ℓ Gen
  FamiliesOn Gen lit .GrammarModel.model = Families
  FamiliesOn Gen lit .GrammarModel.⟦lit⟧ = lit

-- The intended instance: the alphabet interprets itself by its
-- literals.
Literals : GrammarModel (ℓ-suc ℓ-zero) ℓ-zero ℓ-zero Alphabet
Literals = FamiliesOn ℓ-zero Alphabet
  (λ c → literal c , isSetGrammarLiteral c)
