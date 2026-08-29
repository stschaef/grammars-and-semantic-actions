{-# OPTIONS --lossy-unification #-}
{- Guarded recursion.

   A `LaterStr` is a chosen endofunctor ▷ of the model together with
   Löb induction. Because `Semantics.Inductive.Functor` has a code for
   postcomposition with an arbitrary endofunctor, ▷ is usable in
   strictly positive position with no extra syntax: `▷e F = ∘e ▷F F`.

   `isGuarded F` says every recursive variable of F occurs under a ▷.
   For such an F the fixed point is *unique*: by Lambek the initial
   algebra's structure map is already an isomorphism, and guardedness
   is the extra requirement that its inverse be the terminal coalgebra.
   So `GuardedFixpoint F` = initial algebra + terminal coalgebra on the
   same carrier.

   Note there is no `next : A ⊢ ▷ A`. The intended families model reads
   ▷ as "after consuming a nonempty prefix", which is a genuine shift,
   not a delay, so `next` is not available and is not assumed.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Semantics.Model

module Semantics.Later {ℓ ℓ' ℓX} {Gen : hSet ℓX}
  (M : GrammarModel ℓ ℓ' ℓX Gen) where

open import Cubical.Data.Sigma

import Cubical.Categories.Functor as CF

open import Semantics.Notation M
open import Semantics.Inductive.Functor M
open import Semantics.Inductive.Algebra M
open CF.Functor

private
  variable
    X : Type ℓX

------------------------------------------------------------------------
-- Coalgebras (only what is needed to state terminality)
------------------------------------------------------------------------

module _ {X : Type ℓX} (F : X → Functor X) where
  Coalgebra : (X → Grammar) → Type (ℓ-max ℓX ℓ')
  Coalgebra A = ∀ x → A x ⊢ ⟦ F x ⟧ A

  isCoalgHomo : {A B : X → Grammar} (α : Coalgebra A) (β : Coalgebra B)
    → (∀ x → A x ⊢ B x) → Type (ℓ-max ℓX ℓ')
  isCoalgHomo α β ϕ = ∀ x → β x ∘g ϕ x ≡ map (F x) ϕ ∘g α x

  isTerminalCoalgebra : (A : X → Grammar) (α : Coalgebra A)
    → Type (ℓ-max ℓX (ℓ-max ℓ ℓ'))
  isTerminalCoalgebra A α =
    (B : X → Grammar) (β : Coalgebra B)
    → isContr (Σ[ ϕ ∈ (∀ x → B x ⊢ A x) ] isCoalgHomo β α ϕ)

------------------------------------------------------------------------
-- The later modality
------------------------------------------------------------------------

record LaterStr : Type (ℓ-max ℓ ℓ') where
  field
    ▷F : Endo
    -- Löb induction: a guarded self-reference gives a global element.
    lob : {A : Grammar} → ▷F .F-ob A ⊢ A → ⊤ ⊢ A

  ▷ : Grammar → Grammar
  ▷ = ▷F .F-ob

  ▷map : {A B : Grammar} → A ⊢ B → ▷ A ⊢ ▷ B
  ▷map = ▷F .F-hom

  -- ▷ in strictly positive position.
  ▷e : Functor X → Functor X
  ▷e = ∘e ▷F

  ----------------------------------------------------------------
  -- Guardedness: every recursive variable occurs under a ▷.
  ----------------------------------------------------------------
  data isGuarded {X : Type ℓX}
    : Functor X → Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓX)) where
    gk : (A : Grammar) → isGuarded (k A)
    g▷ : (F : Functor X) → isGuarded (▷e F)
    g&e : (Y : hSet ℓX) (F : ⟨ Y ⟩ → Functor X)
        → (∀ y → isGuarded (F y)) → isGuarded (&e Y F)
    g⊕e : (Y : hSet ℓX) (F : ⟨ Y ⟩ → Functor X)
        → (∀ y → isGuarded (F y)) → isGuarded (⊕e Y F)
    g⊗e : {F F' : Functor X}
        → isGuarded F → isGuarded F' → isGuarded (F ⊗e F')
    g∘e : (E : Endo) {F : Functor X}
        → isGuarded F → isGuarded (∘e E F)

  ----------------------------------------------------------------
  -- Unique fixed points
  ----------------------------------------------------------------
  record GuardedFixpoint {X : Type ℓX} (F : X → Functor X)
    : Type (ℓ-max ℓX (ℓ-max ℓ ℓ')) where
    field
      initial : InitialAlgebra F

    open InitialAlgebraNotation initial public

    field
      -- Lambek already makes `unroll` inverse to `roll`; this says it
      -- is moreover the terminal coalgebra, i.e. the fixed point is
      -- unique, not merely initial.
      terminal : isTerminalCoalgebra F μ unroll

    corec : (B : X → Grammar) (β : Coalgebra F B) → ∀ x → B x ⊢ μ x
    corec B β = terminal B β .fst .fst

    corec-homo : (B : X → Grammar) (β : Coalgebra F B)
      → isCoalgHomo F β unroll (corec B β)
    corec-homo B β = terminal B β .fst .snd

    corec-unique : (B : X → Grammar) (β : Coalgebra F B)
      → (ϕ : Σ[ ϕ ∈ (∀ x → B x ⊢ μ x) ] isCoalgHomo F β unroll ϕ)
      → corec B β ≡ ϕ .fst
    corec-unique B β ϕ = cong fst (terminal B β .snd ϕ)

    -- Unique solution principle: any two coalgebra maps into the
    -- fixed point agree.
    solution-unique : (B : X → Grammar) (β : Coalgebra F B)
      → (ϕ ψ : ∀ x → B x ⊢ μ x)
      → isCoalgHomo F β unroll ϕ → isCoalgHomo F β unroll ψ
      → ϕ ≡ ψ
    solution-unique B β ϕ ψ pϕ pψ =
      sym (corec-unique B β (ϕ , pϕ)) ∙ corec-unique B β (ψ , pψ)

  GuardedFixpoints : Type (ℓ-max (ℓ-suc ℓX) (ℓ-max ℓ ℓ'))
  GuardedFixpoints =
    {X : Type ℓX} (F : X → Functor X) → (∀ x → isGuarded (F x))
    → GuardedFixpoint F
