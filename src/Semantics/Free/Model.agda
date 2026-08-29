{-# OPTIONS --lossy-unification #-}
{- The free model on a set of generators.

   `Semantics.Free.Syntax`'s QIT carries exactly the equations a
   `Model` needs, so assembling it is a matter of reading each field
   off a path constructor. Being infinitary in `⊕T`/`&T` puts it at
   `Model (ℓ-suc ℓ) (ℓ-suc ℓ) ℓ`: objects and morphisms one universe
   up, but still indexed by `hSet ℓ`.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Semantics.Free.Model {ℓ} (Gen : hSet ℓ) where

open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Morphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Limits.IndexedProduct.Base

open import Semantics.Model
open import Semantics.Structure.Biclosed
open import Semantics.Structure.IndexedCoproduct
open import Semantics.Free.Syntax Gen

open Category
open Functor
open NatTrans
open NatIso
open isIso
open UniversalElement
open Iso

FREE : Category (ℓ-suc ℓ) (ℓ-suc ℓ)
FREE .ob = Ty
FREE .Hom[_,_] = Exp
FREE .id = idE
FREE ._⋆_ = _⋆E_
FREE .⋆IdL = ⋆IdLE
FREE .⋆IdR = ⋆IdRE
FREE .⋆Assoc = ⋆AssocE
FREE .isSetHom = isSetExp

-- A record expression, not copatterns: the α/η/ρ coherence fields
-- mention their siblings, which the termination checker reads as
-- recursion.
FREEMC : MonoidalCategory (ℓ-suc ℓ) (ℓ-suc ℓ)
FREEMC = record
  { C = FREE
  ; monstr = record
    { tenstr = record
      { ─⊗─ = record
        { F-ob = λ AB → AB .fst ⊗T AB .snd
        ; F-hom = λ fg → fg .fst ⊗E fg .snd
        ; F-id = ⊗E-id
        ; F-seq = λ fg gh → ⊗E-seq (fg .fst) (gh .fst) (fg .snd) (gh .snd)
        }
      ; unit = εT
      }
    ; α = record
      { trans = record { N-ob = λ _ → αE ; N-hom = λ fgh →
          α-nat (fgh .fst) (fgh .snd .fst) (fgh .snd .snd) }
      ; nIso = λ _ → record { inv = αE⁻ ; sec = α-sec ; ret = α-ret }
      }
    ; η = record
      { trans = record { N-ob = λ _ → ηE ; N-hom = η-nat }
      ; nIso = λ _ → record { inv = ηE⁻ ; sec = η-sec ; ret = η-ret }
      }
    ; ρ = record
      { trans = record { N-ob = λ _ → ρE ; N-hom = ρ-nat }
      ; nIso = λ _ → record { inv = ρE⁻ ; sec = ρ-sec ; ret = ρ-ret }
      }
    ; pentagon = λ _ _ _ _ → pentagonE
    ; triangle = λ _ _ → triangleE
    }
  }

------------------------------------------------------------------------
-- Biclosure: β and η are exactly the two round trips.
------------------------------------------------------------------------

⊸Free : (B D : Ty) → ⊸At FREEMC B D
⊸Free B D .vertex = B ⊸T D
⊸Free B D .element = ⊸appE
⊸Free B D .universal A =
  isoToIsEquiv (iso (λ f → (f ⊗E idE) ⋆E ⊸appE) ⊸lamE ⊸βE (λ g → sym (⊸ηE g)))

⟜Free : (A D : Ty) → ⟜At FREEMC A D
⟜Free A D .vertex = D ⟜T A
⟜Free A D .element = ⟜appE
⟜Free A D .universal B =
  isoToIsEquiv (iso (λ f → (idE ⊗E f) ⋆E ⟜appE) ⟜lamE ⟜βE (λ g → sym (⟜ηE g)))

------------------------------------------------------------------------
-- Set-indexed products and coproducts
------------------------------------------------------------------------

ΠFree : (X : hSet ℓ) (A : ⟨ X ⟩ → Ty) → ΠTy FREE A
ΠFree X A .vertex = &T X A
ΠFree X A .element x = πE x
ΠFree X A .universal Γ =
  isoToIsEquiv (iso (λ g x → g ⋆E πE x) &introE
    (λ f → funExt (&βE X A f))
    (λ g → sym (&ηE X A g)))

ΣFree : (X : hSet ℓ) (A : ⟨ X ⟩ → Ty) → ΣTy FREE A
ΣFree X A .vertex = ⊕T X A
ΣFree X A .element x = σE x
ΣFree X A .universal Γ =
  isoToIsEquiv (iso (λ g x → σE x ⋆E g) ⊕elimE
    (λ f → funExt (⊕βE X A f))
    (λ g → sym (⊕ηE X A g)))

------------------------------------------------------------------------

FreeModel : Model (ℓ-suc ℓ) (ℓ-suc ℓ) ℓ
FreeModel .Model.MC = FREEMC
FreeModel .Model.biclosed .Biclosed.⊸ues = ⊸Free
FreeModel .Model.biclosed .Biclosed.⟜ues = ⟜Free
FreeModel .Model.Πs = ΠFree
FreeModel .Model.Σs = ΣFree

Free : GrammarModel (ℓ-suc ℓ) (ℓ-suc ℓ) ℓ Gen
Free .GrammarModel.model = FreeModel
Free .GrammarModel.⟦lit⟧ = ↑_
