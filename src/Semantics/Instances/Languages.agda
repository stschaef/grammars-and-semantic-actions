{-# OPTIONS --lossy-unification #-}
{- The languages model: proof-irrelevant grammars.

   A `Lang ℓ` is a grammar `A : String → Type ℓ` together with a proof
   that every `A w` is a proposition, i.e. a *subset* of `String`. This
   is the classical reading of a grammar: it denotes the language it
   generates, and all the structure of a parse tree is forgotten. A
   parser becomes a mere recogniser.

   The point of this instance is how cheap it is. Because the codomain
   of a term is proof-irrelevant, the hom-type

     Term A B = ∀ w → A .fst w → B .fst w

   is itself a proposition. So:

     - every equation between morphisms holds automatically
       (`isPropHom`), which discharges F-id, F-seq, naturality, the
       isomorphism laws, and the pentagon and triangle coherences;
     - every universal property reduces to giving the two underlying
       maps, since `isEquiv` between propositions follows from a
       logical biimplication (`propBiimpl→Equiv`).

   The connectives are the usual ones, truncated where necessary to
   stay proof-irrelevant:

     A ⊗ B   ↦  ∥ A ⊗ B ∥₁       ε      ↦  ε*   (already a prop)
     ⊕ᴰ      ↦  ∥ ⊕ᴰ ∥₁          &ᴰ     ↦  &ᴰ   (already a prop)
     A ⊸ B   ↦  A ⊸ B            B ⟜ A  ↦  B ⟜ A

   `⊗` and `⊕ᴰ` are the connectives with existential force — "w splits
   as w₁w₂ with ..." and "there is an x with ..." — so they are the
   ones that need truncating; the universally quantified connectives
   `&ᴰ`, `⊸` and `⟜` inherit propositionality from their codomains.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Instances.Languages (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Equiv using (propBiimpl→Equiv)
open import Cubical.Foundations.Structure using (⟨_⟩)

import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Limits.IndexedProduct.Base

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet hiding (⟨_⟩)
open import Grammar.Epsilon.Base Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.LinearFunction.Base Alphabet
open import Grammar.Product.Base Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.Literal.Base Alphabet
open import Term.Base Alphabet as Term

open import Semantics.Model
open import Semantics.Structure.Biclosed
open import Semantics.Structure.IndexedCoproduct

open UniversalElement

private
  variable
    ℓ ℓA ℓB ℓX : Level
    A : Grammar ℓA
    B : Grammar ℓB

----------------------------------------------------------------
-- Terms into a language form a proposition. This single fact is
-- what makes the whole model go through.
----------------------------------------------------------------
isPropTerm : isLang B → isProp (A ⊢ B)
isPropTerm isLangB = isPropΠ λ w → isPropΠ λ _ → isLangB w

----------------------------------------------------------------
-- Pointwise propositional truncation of a grammar: the language of
-- words that admit *some* parse.
----------------------------------------------------------------
∥_∥L : Grammar ℓA → Grammar ℓA
∥ A ∥L w = PT.∥ A w ∥₁

isLang∥∥L : isLang ∥ A ∥L
isLang∥∥L w = PT.isPropPropTrunc

truncL : A ⊢ ∥ A ∥L
truncL w x = PT.∣ x ∣₁

recL : isLang B → A ⊢ B → ∥ A ∥L ⊢ B
recL isLangB f w = PT.rec (isLangB w) (f w)

mapL : A ⊢ B → ∥ A ∥L ⊢ ∥ B ∥L
mapL f = recL isLang∥∥L (truncL ∘g f)

----------------------------------------------------------------
-- Truncation is a lax monoidal functor: it can be pushed out of
-- either side of a linear product. (The other direction is the
-- interesting one and is false in general, but we never need it.)
----------------------------------------------------------------
opaque
  unfolding _⊗_
  ∥∥L⊗ : ∥ A ∥L ⊗ B ⊢ ∥ A ⊗ B ∥L
  ∥∥L⊗ w (s , a , b) = PT.map (λ a' → s , a' , b) a

  ⊗∥∥L : A ⊗ ∥ B ∥L ⊢ ∥ A ⊗ B ∥L
  ⊗∥∥L w (s , a , b) = PT.map (λ b' → s , a , b') b

----------------------------------------------------------------
-- The universally quantified connectives are already prop-valued.
----------------------------------------------------------------
opaque
  unfolding _⊸_ _⟜_
  isLang⊸ : isLang B → isLang (A ⊸ B)
  isLang⊸ isLangB w = isPropΠ λ _ → isPropΠ λ _ → isLangB _

  isLang⟜ : isLang A → isLang (A ⟜ B)
  isLang⟜ isLangA w = isPropΠ λ _ → isPropΠ λ _ → isLangA _

isLang&ᴰ : {X : Type ℓX} {A : X → Grammar ℓA}
  → (∀ x → isLang (A x)) → isLang (&ᴰ A)
isLang&ᴰ isLangA w = isPropΠ λ x → isLangA x w

----------------------------------------------------------------
module _ (ℓ : Level) where
  open Category
  open Functor
  open NatTrans
  open NatIso
  open isIso

  ----------------------------------------------------------------
  -- The category of languages and terms.
  ----------------------------------------------------------------
  LANG : Category (ℓ-suc ℓ) ℓ
  LANG .ob = Lang ℓ
  LANG .Hom[_,_] A B = A .fst ⊢ B .fst
  LANG .Category.id = Term.id
  LANG ._⋆_ = Term.seq
  LANG .⋆IdL _ = refl
  LANG .⋆IdR _ = refl
  LANG .⋆Assoc _ _ _ = refl
  LANG .isSetHom {y = B} = isProp→isSet (isPropTerm (B .snd))

  ----------------------------------------------------------------
  -- The monoidal structure: the truncated linear product.
  --
  -- Every diagram in LANG commutes, so all the coherence data below
  -- is `isPropTerm` applied to the `isLang` proof of the codomain.
  -- That codomain is a tensor everywhere except in the naturality
  -- squares of η and ρ and in their `sec`s.
  ----------------------------------------------------------------
  _⊛_ : Lang ℓ → Lang ℓ → Lang ℓ
  A ⊛ B = ∥ A .fst ⊗ B .fst ∥L , isLang∥∥L

  εL : Lang ℓ
  εL = ε* , isLangε*

  private
    ⊛hom : {A B A' B' : Lang ℓ}
         → LANG [ A , A' ] → LANG [ B , B' ] → LANG [ A ⊛ B , A' ⊛ B' ]
    ⊛hom f g = mapL (f ,⊗ g)

    αL : (A B C : Lang ℓ) → LANG [ A ⊛ (B ⊛ C) , (A ⊛ B) ⊛ C ]
    αL A B C = recL isLang∥∥L (mapL (truncL ,⊗ Term.id ∘g ⊗-assoc) ∘g ⊗∥∥L)

    αL⁻ : (A B C : Lang ℓ) → LANG [ (A ⊛ B) ⊛ C , A ⊛ (B ⊛ C) ]
    αL⁻ A B C = recL isLang∥∥L (mapL (Term.id ,⊗ truncL ∘g ⊗-assoc⁻) ∘g ∥∥L⊗)

    ηL : (A : Lang ℓ) → LANG [ εL ⊛ A , A ]
    ηL A = recL (A .snd) ⊗-unit*-l

    ηL⁻ : (A : Lang ℓ) → LANG [ A , εL ⊛ A ]
    ηL⁻ A = truncL ∘g ⊗-unit*-l⁻

    ρL : (A : Lang ℓ) → LANG [ A ⊛ εL , A ]
    ρL A = recL (A .snd) ⊗-unit*-r

    ρL⁻ : (A : Lang ℓ) → LANG [ A , A ⊛ εL ]
    ρL⁻ A = truncL ∘g ⊗-unit*-r⁻

  -- Given as a record expression rather than by copatterns, following
  -- `Semantics.Instances.Sets`: the coherence fields have types
  -- mentioning their siblings.
  LANGMC : MonoidalCategory (ℓ-suc ℓ) ℓ
  LANGMC = record
    { C = LANG
    ; monstr = record
      { tenstr = record
        { ─⊗─ = record
          { F-ob = λ AB → AB .fst ⊛ AB .snd
          ; F-hom = λ fg → ⊛hom (fg .fst) (fg .snd)
          ; F-id = isPropTerm isLang∥∥L _ _
          ; F-seq = λ _ _ → isPropTerm isLang∥∥L _ _
          }
        ; unit = εL
        }
      ; α = record
        { trans = record
          { N-ob = λ ABC → αL (ABC .fst) (ABC .snd .fst) (ABC .snd .snd)
          ; N-hom = λ _ → isPropTerm isLang∥∥L _ _
          }
        ; nIso = λ ABC → record
          { inv = αL⁻ (ABC .fst) (ABC .snd .fst) (ABC .snd .snd)
          ; sec = isPropTerm isLang∥∥L _ _
          ; ret = isPropTerm isLang∥∥L _ _
          }
        }
      ; η = record
        { trans = record
          { N-ob = ηL ; N-hom = λ {_} {y} _ → isPropTerm (y .snd) _ _ }
        ; nIso = λ A → record
          { inv = ηL⁻ A
          ; sec = isPropTerm (A .snd) _ _
          ; ret = isPropTerm isLang∥∥L _ _
          }
        }
      ; ρ = record
        { trans = record
          { N-ob = ρL ; N-hom = λ {_} {y} _ → isPropTerm (y .snd) _ _ }
        ; nIso = λ A → record
          { inv = ρL⁻ A
          ; sec = isPropTerm (A .snd) _ _
          ; ret = isPropTerm isLang∥∥L _ _
          }
        }
      ; pentagon = λ _ _ _ _ → isPropTerm isLang∥∥L _ _
      ; triangle = λ _ _ → isPropTerm isLang∥∥L _ _
      }
    }

  ----------------------------------------------------------------
  -- The biclosure is ⊸ and ⟜, untruncated. Both universal
  -- properties are biimplications between propositions.
  ----------------------------------------------------------------
  ⊸Lang : (B D : Lang ℓ) → ⊸At LANGMC B D
  ⊸Lang B D .vertex = (B .fst ⊸ D .fst) , isLang⊸ (D .snd)
  ⊸Lang B D .element = recL (D .snd) ⊸-app
  ⊸Lang B D .universal A =
    propBiimpl→Equiv
      (isPropTerm (isLang⊸ (D .snd)))
      (isPropTerm (D .snd))
      _
      (λ f → ⊸-intro (f ∘g truncL))
      .snd

  ⟜Lang : (A D : Lang ℓ) → ⟜At LANGMC A D
  ⟜Lang A D .vertex = (D .fst ⟜ A .fst) , isLang⟜ (D .snd)
  ⟜Lang A D .element = recL (D .snd) ⟜-app
  ⟜Lang A D .universal B =
    propBiimpl→Equiv
      (isPropTerm (isLang⟜ (D .snd)))
      (isPropTerm (D .snd))
      _
      (λ f → ⟜-intro (f ∘g truncL))
      .snd

  ----------------------------------------------------------------
  -- Set-indexed products are &ᴰ; set-indexed coproducts are the
  -- truncation of ⊕ᴰ.
  ----------------------------------------------------------------
  ΠLang : (X : hSet ℓ) (A : ⟨ X ⟩ → Lang ℓ) → ΠTy LANG A
  ΠLang X A .vertex =
    (&[ x ∈ ⟨ X ⟩ ] (A x .fst)) , isLang&ᴰ (λ x → A x .snd)
  ΠLang X A .element x = π x
  ΠLang X A .universal Γ =
    propBiimpl→Equiv
      (isPropTerm (isLang&ᴰ (λ x → A x .snd)))
      (isPropΠ (λ x → isPropTerm (A x .snd)))
      _
      &ᴰ-intro
      .snd

  ΣLang : (X : hSet ℓ) (A : ⟨ X ⟩ → Lang ℓ) → ΣTy LANG A
  ΣLang X A .vertex = ∥ (⊕[ x ∈ ⟨ X ⟩ ] (A x .fst)) ∥L , isLang∥∥L
  ΣLang X A .element x = truncL ∘g σ x
  ΣLang X A .universal Γ =
    propBiimpl→Equiv
      (isPropTerm (Γ .snd))
      (isPropΠ (λ x → isPropTerm (Γ .snd)))
      _
      (λ f → recL (Γ .snd) (⊕ᴰ-elim f))
      .snd

  ----------------------------------------------------------------
  Languages : Model (ℓ-suc ℓ) ℓ ℓ
  Languages .Model.MC = LANGMC
  Languages .Model.biclosed .Biclosed.⊸ues = ⊸Lang
  Languages .Model.biclosed .Biclosed.⟜ues = ⟜Lang
  Languages .Model.Πs = ΠLang
  Languages .Model.Σs = ΣLang

  LanguagesOn : (Gen : hSet ℓ) (lit : ⟨ Gen ⟩ → Lang ℓ)
    → GrammarModel (ℓ-suc ℓ) ℓ ℓ Gen
  LanguagesOn Gen lit .GrammarModel.model = Languages
  LanguagesOn Gen lit .GrammarModel.⟦lit⟧ = lit

-- The intended instance: each character denotes the singleton
-- language {[ c ]}, which is already proof-irrelevant.
Literals : GrammarModel (ℓ-suc ℓ-zero) ℓ-zero ℓ-zero Alphabet
Literals = LanguagesOn ℓ-zero Alphabet
  (λ c → literal c , isLangLiteral c)
