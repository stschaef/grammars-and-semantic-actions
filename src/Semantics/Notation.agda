{-# OPTIONS --lossy-unification #-}
{- The grammar DSL, in an arbitrary model.

   This is the vocabulary that `Grammar.*` provides for families of
   sets over strings, but every definition here is by universal
   property, so it makes sense in any `GrammarModel`.

   In particular ⊤, ⊥, & and ⊕ are *not* primitive: they are the
   set-indexed (co)products over the empty type and over `Bool`.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Semantics.Model

module Semantics.Notation {ℓ ℓ' ℓX} {Gen : hSet ℓX}
  (M : GrammarModel ℓ ℓ' ℓX Gen) where

open import Cubical.Data.Bool using (Bool; true; false; isSetBool)
open import Cubical.Data.List using (List; []; _∷_)
import Cubical.Data.Empty as Empty

open import Cubical.Categories.Category
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Limits.IndexedProduct.Base
open import Cubical.Categories.Presheaf.Representable using (UniversalElement)

open import Semantics.Structure.Biclosed
open import Semantics.Structure.IndexedCoproduct

open GrammarModel M
open MonoidalCategory MC public hiding (C)
open Biclosed biclosed public

------------------------------------------------------------------------
-- Grammars and terms
------------------------------------------------------------------------

Grammar : Type ℓ
Grammar = ob

infix 1 _⊢_
_⊢_ : Grammar → Grammar → Type ℓ'
A ⊢ B = Hom[ A , B ]

infixr 9 _∘g_
_∘g_ : ∀ {A B D} → B ⊢ D → A ⊢ B → A ⊢ D
f ∘g g = g ⋆ f

private
  variable
    A B D E : Grammar

------------------------------------------------------------------------
-- ⊗ and ε: the monoidal structure
------------------------------------------------------------------------

ε : Grammar
ε = unit

infixr 20 _,⊗_
_,⊗_ : A ⊢ B → D ⊢ E → A ⊗ D ⊢ B ⊗ E
_,⊗_ = _⊗ₕ_

⊗-assoc : A ⊗ (B ⊗ D) ⊢ (A ⊗ B) ⊗ D
⊗-assoc = α⟨ _ , _ , _ ⟩

⊗-assoc⁻ : (A ⊗ B) ⊗ D ⊢ A ⊗ (B ⊗ D)
⊗-assoc⁻ = α⁻¹⟨ _ , _ , _ ⟩

⊗-unit-l : ε ⊗ A ⊢ A
⊗-unit-l = η⟨ _ ⟩

⊗-unit-l⁻ : A ⊢ ε ⊗ A
⊗-unit-l⁻ = η⁻¹⟨ _ ⟩

⊗-unit-r : A ⊗ ε ⊢ A
⊗-unit-r = ρ⟨ _ ⟩

⊗-unit-r⁻ : A ⊢ A ⊗ ε
⊗-unit-r⁻ = ρ⁻¹⟨ _ ⟩

------------------------------------------------------------------------
-- ⊕ᴰ: set-indexed coproducts
------------------------------------------------------------------------

infix 8 ⊕ᴰ
⊕ᴰ : {X : hSet ℓX} → (⟨ X ⟩ → Grammar) → Grammar
⊕ᴰ {X = X} A = UniversalElement.vertex (Σs X A)

syntax ⊕ᴰ {X = X} (λ x → A) = ⊕[ x ∈ X ] A

module _ {X : hSet ℓX} {A : ⟨ X ⟩ → Grammar} where
  private module s = ΣTyNotation A (Σs X A)

  σ : ∀ x → A x ⊢ ⊕ᴰ A
  σ = s.σ

  ⊕ᴰ-elim : (∀ x → A x ⊢ B) → ⊕ᴰ A ⊢ B
  ⊕ᴰ-elim = s.elim

  ⊕ᴰ-β : (f : ∀ x → A x ⊢ B) (x : ⟨ X ⟩) → ⊕ᴰ-elim f ∘g σ x ≡ f x
  ⊕ᴰ-β = s.⊕β

  ⊕ᴰ≡ : {f f' : ⊕ᴰ A ⊢ B} → (∀ x → f ∘g σ x ≡ f' ∘g σ x) → f ≡ f'
  ⊕ᴰ≡ = s.⊕ext

------------------------------------------------------------------------
-- &ᴰ: set-indexed products
------------------------------------------------------------------------

infix 7 &ᴰ
&ᴰ : {X : hSet ℓX} → (⟨ X ⟩ → Grammar) → Grammar
&ᴰ {X = X} A = UniversalElement.vertex (Πs X A)

syntax &ᴰ {X = X} (λ x → A) = &[ x ∈ X ] A

module _ {X : hSet ℓX} {A : ⟨ X ⟩ → Grammar} where
  private module p = ΠTyNotation A (Πs X A)

  π : ∀ x → &ᴰ A ⊢ A x
  π = p.app

  &ᴰ-intro : (∀ x → B ⊢ A x) → B ⊢ &ᴰ A
  &ᴰ-intro = p.lda

  &ᴰ-β : (f : ∀ x → B ⊢ A x) (x : ⟨ X ⟩) → π x ∘g &ᴰ-intro f ≡ f x
  &ᴰ-β = p.Πβ

  &ᴰ≡ : {f f' : B ⊢ &ᴰ A} → (∀ x → π x ∘g f ≡ π x ∘g f') → f ≡ f'
  &ᴰ≡ q = p.extensionality (funExt q)

------------------------------------------------------------------------
-- ⊤, ⊥, & and ⊕ are derived, not primitive
------------------------------------------------------------------------

-- The index sets used to derive the nullary and binary connectives.
Empty* : hSet ℓX
Empty* = Empty.⊥* , isProp→isSet Empty.isProp⊥*

Two : hSet ℓX
Two = Lift ℓX Bool , isOfHLevelLift 2 isSetBool

pair : Grammar → Grammar → ⟨ Two ⟩ → Grammar
pair A B (lift true) = A
pair A B (lift false) = B

⊤ : Grammar
⊤ = &ᴰ {X = Empty*} Empty.rec*

⊤-intro : A ⊢ ⊤
⊤-intro = &ᴰ-intro Empty.elim*

⊥ : Grammar
⊥ = ⊕ᴰ {X = Empty*} Empty.rec*

⊥-elim : ⊥ ⊢ A
⊥-elim = ⊕ᴰ-elim Empty.elim*

infixr 6 _&_
_&_ : Grammar → Grammar → Grammar
A & B = &ᴰ {X = Two} (pair A B)

π₁ : A & B ⊢ A
π₁ = π (lift true)

π₂ : A & B ⊢ B
π₂ = π (lift false)

_,&_ : A ⊢ B → A ⊢ D → A ⊢ B & D
f ,& g = &ᴰ-intro (λ where
  (lift true) → f
  (lift false) → g)

infixr 5 _⊕_
_⊕_ : Grammar → Grammar → Grammar
A ⊕ B = ⊕ᴰ {X = Two} (pair A B)

inl : A ⊢ A ⊕ B
inl = σ (lift true)

inr : B ⊢ A ⊕ B
inr = σ (lift false)

⊕-elim : A ⊢ D → B ⊢ D → A ⊕ B ⊢ D
⊕-elim f g = ⊕ᴰ-elim (λ where
  (lift true) → f
  (lift false) → g)

------------------------------------------------------------------------
-- Generators
------------------------------------------------------------------------

literal : ⟨ Gen ⟩ → Grammar
literal = ⟦lit⟧

＂_＂ : ⟨ Gen ⟩ → Grammar
＂ c ＂ = literal c

char : Grammar
char = ⊕[ c ∈ Gen ] literal c

-- The grammar of exactly the word w. This makes sense in any model:
-- it is a ⊗-fold of literals, with no strings involved.
⌈_⌉ : List ⟨ Gen ⟩ → Grammar
⌈ [] ⌉ = ε
⌈ c ∷ w ⌉ = literal c ⊗ ⌈ w ⌉

------------------------------------------------------------------------
-- Functoriality of ⊗, and the transposes
------------------------------------------------------------------------

open import Cubical.Data.Sigma using (_,_)
open import Cubical.Categories.Functor using (Functor)
open Functor

,⊗-id : id {A} ,⊗ id {B} ≡ id
,⊗-id = ─⊗─ .F-id

,⊗-seq : ∀ {A A' A'' B B' B''}
  (f : A ⊢ A') (f' : A' ⊢ A'') (g : B ⊢ B') (g' : B' ⊢ B'')
  → (f' ∘g f) ,⊗ (g' ∘g g) ≡ (f' ,⊗ g') ∘g (f ,⊗ g)
,⊗-seq f f' g g' = ─⊗─ .F-seq (f , g) (f' , g')

-- Composing on the left factor only.
,⊗-comp-l : ∀ {A A' A'' B} (f : A ⊢ A') (f' : A' ⊢ A'')
  → (f' ,⊗ id {B}) ∘g (f ,⊗ id) ≡ (f' ∘g f) ,⊗ id
,⊗-comp-l {B = B} f f' =
  sym (,⊗-seq f f' id id) ∙ cong ((f' ∘g f) ,⊗_) (⋆IdL (id {B}))

-- Composing on the right factor only.
,⊗-comp-r : ∀ {A B B' B''} (g : B ⊢ B') (g' : B' ⊢ B'')
  → (id {A} ,⊗ g') ∘g (id ,⊗ g) ≡ id ,⊗ (g' ∘g g)
,⊗-comp-r {A = A} g g' =
  sym (,⊗-seq id id g g') ∙ cong (_,⊗ (g' ∘g g)) (⋆IdL (id {A}))

⊸-intro⁻ : A ⊢ B ⊸ D → A ⊗ B ⊢ D
⊸-intro⁻ f = ⊸-app ∘g (f ,⊗ id)

⟜-intro⁻ : B ⊢ D ⟜ A → A ⊗ B ⊢ D
⟜-intro⁻ f = ⟜-app ∘g (id ,⊗ f)

∘g-assoc : ∀ {A B D E} (h : D ⊢ E) (g : B ⊢ D) (f : A ⊢ B)
  → (h ∘g g) ∘g f ≡ h ∘g (g ∘g f)
∘g-assoc h g f = sym (⋆Assoc f g h)

∘g-idL : ∀ {A B} (f : A ⊢ B) → id ∘g f ≡ f
∘g-idL = ⋆IdR

∘g-idR : ∀ {A B} (f : A ⊢ B) → f ∘g id ≡ f
∘g-idR = ⋆IdL
