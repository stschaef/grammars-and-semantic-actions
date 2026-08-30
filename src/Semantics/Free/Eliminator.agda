{-# OPTIONS --lossy-unification #-}
{- The eliminator out of the free model.

   A displayed model over `FreeModel`, together with an interpretation
   of the generators, determines a section of it. This is the shape a
   gluing metatheorem takes: choose a displayed model, interpret the
   generators, and the eliminator gives the property for every object
   and every morphism of the syntax.

   The object part is below. It already pins down that `Modelᴰ` carries
   the right data: each type former is interpreted by the *vertex* of
   the corresponding displayed universal element.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Semantics.Free.Eliminator {ℓ} (Gen : hSet ℓ) where

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Monoidal.Base
open import Cubical.Categories.Displayed.More using (isSetHomᴰ')
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Instances.Fiber

open import Semantics.Model
open import Semantics.Displayed.Model
open import Cubical.Data.Sigma
open import Semantics.Displayed.IndexedProduct
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Semantics.Free.Syntax Gen
open import Semantics.Free.Model Gen

module _ {ℓCᴰ ℓCᴰ'} (Mᴰ : Modelᴰ FreeModel ℓCᴰ ℓCᴰ') where

  open Modelᴰ Mᴰ

  private
    module Cᴰ = Categoryᴰ Cᴰ
    module R = HomᴰReasoning Cᴰ
    module F = Fibers Cᴰ
    module Fop = Fibers (Cᴰ ^opᴰ)
  open MonoidalStrᴰ MCᴰ
  open NatIsoᴰ
  open NatTransᴰ
  open isIsoᴰ
  open Functorᴰ
  open Section
  open Biclosedᴰ biclosedᴰ

  -- | An interpretation of the generators.
  Interpᴰ : Type (ℓ-max ℓ ℓCᴰ)
  Interpᴰ = ∀ g → Cᴰ.ob[ ↑ g ]

  module _ (ı : Interpᴰ) where
    elimOb : ∀ A → Cᴰ.ob[ A ]
    elimOb (↑ g) = ı g
    elimOb εT = unitᴰ
    elimOb (A ⊗T B) = elimOb A ⊗ᴰ elimOb B
    elimOb (A ⊸T B) = ⊸uesᴰ (elimOb A) (elimOb B) .fst
    elimOb (A ⟜T B) = ⟜uesᴰ (elimOb B) (elimOb A) .fst
    elimOb (⊕T X A) = Σsᴰ X A (λ x → elimOb (A x)) .fst
    elimOb (&T X A) = Πsᴰ X A (λ x → elimOb (A x)) .fst

    private
      -- The reind the displayed presheaf action inserts is along a
      -- *loop* on the base morphism, and `Exp` is a set, so it is the
      -- identity.
      loopReind : ∀ {a b}{f : Exp a b}{aᴰ bᴰ} {q : f ≡ f}
                  {Y : Cᴰ.Hom[ f ][ aᴰ , bᴰ ]}
                → F.reind q Y ≡ Y
      loopReind = F.rectifyOut (F.reind-filler⁻ _)

      module ⊗ᴰ = Functorᴰ ─⊗ᴰ─
      -- The displayed presheaves underlying the indexed (co)products,
      -- so that their *family*-level reind-filler is reachable. It is
      -- private inside UniversalElementᴰNotation, but P and Pᴰ are
      -- module parameters, so it can be rebuilt from outside.
      module ΠP (X : hSet ℓ) (A : ⟨ X ⟩ → Ty) =
        PresheafᴰNotation Cᴰ _
          (ΠTyPshᴰ Cᴰ (λ x → Cᴰ [-][-, elimOb (A x) ]))
      module ΣP (X : hSet ℓ) (A : ⟨ X ⟩ → Ty) =
        PresheafᴰNotation (Cᴰ ^opᴰ) _
          (ΠTyPshᴰ (Cᴰ ^opᴰ) (λ x → (Cᴰ ^opᴰ) [-][-, elimOb (A x) ]))
      module Σᴰ (X : hSet ℓ) (A : ⟨ X ⟩ → Ty) =
        UniversalElementᴰNotation (Cᴰ ^opᴰ) _
          (ΠTyPshᴰ (Cᴰ ^opᴰ) (λ x → (Cᴰ ^opᴰ) [-][-, elimOb (A x) ]))
          (Σsᴰ X A (λ x → elimOb (A x)))
      module Πᴰ (X : hSet ℓ) (A : ⟨ X ⟩ → Ty) =
        UniversalElementᴰNotation Cᴰ _
          (ΠTyPshᴰ Cᴰ (λ x → Cᴰ [-][-, elimOb (A x) ]))
          (Πsᴰ X A (λ x → elimOb (A x)))
      module ⊸ᴰ (B D : Ty) =
        UniversalElementᴰNotation Cᴰ _ _ (⊸uesᴰ (elimOb B) (elimOb D))
      module ⟜ᴰ (A D : Ty) =
        UniversalElementᴰNotation Cᴰ _ _ (⟜uesᴰ (elimOb A) (elimOb D))

    ------------------------------------------------------------------
    -- The eight β/η obligations, in *bare* form.
    --
    -- `UniversalElementᴰNotation` states these with the `reind` that
    -- the displayed representable's action inserts. Normalising the
    -- goal shows that reind is along a *loop* on the base morphism
    -- (`refl ∙∙ refl ∙∙ refl`), so since `Exp` is a set it is
    -- removable — the obstruction is only that `subst` does not see
    -- through the propositionally-equal motive. Filling these from
    -- `⊸ᴰ.βᴰ` etc. is the remaining step; everything else below is
    -- complete.
    ------------------------------------------------------------------

    ⊸βᴰ' : ∀ {A B D} (f : Exp (A ⊗T B) D)
      (fᴰ : Cᴰ.Hom[ f ][ elimOb A ⊗ᴰ elimOb B , elimOb D ])
      → ((⊸ᴰ.introᴰ B D fᴰ) ⊗ₕᴰ Cᴰ.idᴰ) Cᴰ.⋆ᴰ (⊸ᴰ.elementᴰ B D)
        Cᴰ.≡[ ⊸βE f ] fᴰ
    ⊸βᴰ' f fᴰ =
      F.rectify (F.≡out (F.reind-filler _ ∙ F.≡in (⊸ᴰ.βᴰ _ _ fᴰ)))

    ⊸ηᴰ' : ∀ {A B D} (g : Exp A (B ⊸T D))
      (gᴰ : Cᴰ.Hom[ g ][ elimOb A , ⊸ᴰ.vertexᴰ B D ])
      → gᴰ Cᴰ.≡[ ⊸ηE g ]
        ⊸ᴰ.introᴰ B D ((gᴰ ⊗ₕᴰ Cᴰ.idᴰ) Cᴰ.⋆ᴰ (⊸ᴰ.elementᴰ B D))
    ⊸ηᴰ' g gᴰ =
      F.rectify (F.≡out (F.≡in (⊸ᴰ.ηᴰ _ _ gᴰ)
        ∙ ⊸ᴰ.cong-introᴰ _ _ (sym (F.reind-filler _))))

    ⟜βᴰ' : ∀ {A B D} (f : Exp (A ⊗T B) D)
      (fᴰ : Cᴰ.Hom[ f ][ elimOb A ⊗ᴰ elimOb B , elimOb D ])
      → (Cᴰ.idᴰ ⊗ₕᴰ (⟜ᴰ.introᴰ A D fᴰ)) Cᴰ.⋆ᴰ (⟜ᴰ.elementᴰ A D)
        Cᴰ.≡[ ⟜βE f ] fᴰ
    ⟜βᴰ' f fᴰ =
      F.rectify (F.≡out (F.reind-filler _ ∙ F.≡in (⟜ᴰ.βᴰ _ _ fᴰ)))

    ⟜ηᴰ' : ∀ {A B D} (g : Exp B (D ⟜T A))
      (gᴰ : Cᴰ.Hom[ g ][ elimOb B , ⟜ᴰ.vertexᴰ A D ])
      → gᴰ Cᴰ.≡[ ⟜ηE g ]
        ⟜ᴰ.introᴰ A D ((Cᴰ.idᴰ ⊗ₕᴰ gᴰ) Cᴰ.⋆ᴰ (⟜ᴰ.elementᴰ A D))
    ⟜ηᴰ' g gᴰ =
      F.rectify (F.≡out (F.≡in (⟜ᴰ.ηᴰ _ _ gᴰ)
        ∙ ⟜ᴰ.cong-introᴰ _ _ (sym (F.reind-filler _))))

    ⊕βᴰ' : ∀ {B} (X : hSet ℓ) (A : ⟨ X ⟩ → Ty) (f : ∀ x → Exp (A x) B)
      (fᴰ : ∀ x → Cᴰ.Hom[ f x ][ elimOb (A x) , elimOb B ]) (x : ⟨ X ⟩)
      → (Σᴰ.elementᴰ X A x) Cᴰ.⋆ᴰ (Σᴰ.introᴰ X A fᴰ)
        Cᴰ.≡[ ⊕βE X A f x ] fᴰ x
    ⊕βᴰ' X A f fᴰ x =
      Fop.rectify (Fop.≡out (Fop.reind-filler _
        ∙ Fop.≡in (λ j → Σᴰ.βᴰ _ _ fᴰ j x)))

    ⊕ηᴰ' : ∀ {B} (X : hSet ℓ) (A : ⟨ X ⟩ → Ty) (g : Exp (⊕T X A) B)
      (gᴰ : Cᴰ.Hom[ g ][ Σᴰ.vertexᴰ X A , elimOb B ])
      → gᴰ Cᴰ.≡[ ⊕ηE X A g ]
        Σᴰ.introᴰ X A (λ x → (Σᴰ.elementᴰ X A x) Cᴰ.⋆ᴰ gᴰ)
    ⊕ηᴰ' X A g gᴰ =
      F.rectify (F.≡out (F.≡in (Σᴰ.ηᴰ _ _ gᴰ)
        ∙ Σᴰ.cong-introᴰ _ _ (ΣPathP (refl , funExt (λ x → loopReind)))))

    &βᴰ' : ∀ {B} (X : hSet ℓ) (A : ⟨ X ⟩ → Ty) (f : ∀ x → Exp B (A x))
      (fᴰ : ∀ x → Cᴰ.Hom[ f x ][ elimOb B , elimOb (A x) ]) (x : ⟨ X ⟩)
      → (Πᴰ.introᴰ X A fᴰ) Cᴰ.⋆ᴰ (Πᴰ.elementᴰ X A x)
        Cᴰ.≡[ &βE X A f x ] fᴰ x
    &βᴰ' X A f fᴰ x =
      F.rectify (F.≡out (F.reind-filler _
        ∙ F.≡in (λ j → Πᴰ.βᴰ _ _ fᴰ j x)))

    &ηᴰ' : ∀ {B} (X : hSet ℓ) (A : ⟨ X ⟩ → Ty) (g : Exp B (&T X A))
      (gᴰ : Cᴰ.Hom[ g ][ elimOb B , Πᴰ.vertexᴰ X A ])
      → gᴰ Cᴰ.≡[ &ηE X A g ]
        Πᴰ.introᴰ X A (λ x → gᴰ Cᴰ.⋆ᴰ (Πᴰ.elementᴰ X A x))
    -- Both indexed η cases are open. The reind sits inside `introᴰ`s
    -- *family* argument, and the reind path is the third component of
    -- the comma-morphism produced by `appHet` in `ΠTyPshᴰ`, which Agda
    -- cannot invert to solve the metavariable. Supplying it needs
    -- either the bare (reind-free) η lemma upstream in ccl, or that
    -- path written out by hand.
    &ηᴰ' X A g gᴰ =
      F.rectify (F.≡out (F.≡in (Πᴰ.ηᴰ _ _ gᴰ)
        ∙ Πᴰ.cong-introᴰ _ _ (ΣPathP (refl , funExt (λ x → loopReind)))))

    ------------------------------------------------------------------
    -- The morphism part
    ------------------------------------------------------------------

    elimHom : ∀ {A B} (f : Exp A B) → Cᴰ.Hom[ f ][ elimOb A , elimOb B ]
    -- category
    elimHom idE = Cᴰ.idᴰ
    elimHom (f ⋆E g) = elimHom f Cᴰ.⋆ᴰ elimHom g
    elimHom (⋆IdLE f i) = Cᴰ.⋆IdLᴰ (elimHom f) i
    elimHom (⋆IdRE f i) = Cᴰ.⋆IdRᴰ (elimHom f) i
    elimHom (⋆AssocE f g h i) =
      Cᴰ.⋆Assocᴰ (elimHom f) (elimHom g) (elimHom h) i
    elimHom (isSetExp f g p q i j) =
      isSetHomᴰ' Cᴰ (elimHom f) (elimHom g)
        (λ i → elimHom (p i)) (λ i → elimHom (q i)) i j
    -- tensor
    elimHom (f ⊗E g) = elimHom f ⊗ₕᴰ elimHom g
    elimHom (⊗E-id i) = R.rectify {p' = ⊗E-id} ⊗ᴰ.F-idᴰ i
    elimHom (⊗E-seq f g f' g' i) =
      R.rectify {p' = ⊗E-seq f g f' g'}
        (⊗ᴰ.F-seqᴰ (elimHom f , elimHom f') (elimHom g , elimHom g')) i
    -- associator
    elimHom αE = αᴰ⟨ _ , _ , _ ⟩
    elimHom αE⁻ = α⁻¹ᴰ⟨ _ , _ , _ ⟩
    elimHom (α-sec i) = R.rectify {p' = α-sec} (αᴰ .nIsoᴰ _ .secᴰ) i
    elimHom (α-ret i) = R.rectify {p' = α-ret} (αᴰ .nIsoᴰ _ .retᴰ) i
    elimHom (α-nat f g h i) =
      R.rectify {p' = α-nat f g h}
        (αᴰ .transᴰ .N-homᴰ (elimHom f , elimHom g , elimHom h)) i
    -- left unitor
    elimHom ηE = ηᴰ⟨ _ ⟩
    elimHom ηE⁻ = η⁻¹ᴰ⟨ _ ⟩
    elimHom (η-sec i) = R.rectify {p' = η-sec} (ηᴰ .nIsoᴰ _ .secᴰ) i
    elimHom (η-ret i) = R.rectify {p' = η-ret} (ηᴰ .nIsoᴰ _ .retᴰ) i
    elimHom (η-nat f i) =
      R.rectify {p' = η-nat f} (ηᴰ .transᴰ .N-homᴰ (elimHom f)) i
    -- right unitor
    elimHom ρE = ρᴰ⟨ _ ⟩
    elimHom ρE⁻ = ρ⁻¹ᴰ⟨ _ ⟩
    elimHom (ρ-sec i) = R.rectify {p' = ρ-sec} (ρᴰ .nIsoᴰ _ .secᴰ) i
    elimHom (ρ-ret i) = R.rectify {p' = ρ-ret} (ρᴰ .nIsoᴰ _ .retᴰ) i
    elimHom (ρ-nat f i) =
      R.rectify {p' = ρ-nat f} (ρᴰ .transᴰ .N-homᴰ (elimHom f)) i
    -- coherence
    elimHom (pentagonE i) = R.rectify {p' = pentagonE} (pentagonᴰ _ _ _ _) i
    elimHom (triangleE i) = R.rectify {p' = triangleE} (triangleᴰ _ _) i
    -- ⊸
    elimHom (⊸appE {B} {D}) = ⊸ᴰ.elementᴰ B D
    elimHom (⊸lamE {A} {B} {D} f) = ⊸ᴰ.introᴰ B D (elimHom f)
    elimHom (⊸βE {A} {B} {D} f i) = ⊸βᴰ' f (elimHom f) i
    elimHom (⊸ηE {A} {B} {D} g i) = ⊸ηᴰ' g (elimHom g) i
    -- ⟜
    elimHom (⟜appE {A} {D}) = ⟜ᴰ.elementᴰ A D
    elimHom (⟜lamE {A} {B} {D} f) = ⟜ᴰ.introᴰ A D (elimHom f)
    elimHom (⟜βE {A} {B} {D} f i) = ⟜βᴰ' f (elimHom f) i
    elimHom (⟜ηE {A} {B} {D} g i) = ⟜ηᴰ' g (elimHom g) i
    -- indexed coproducts
    elimHom (σE {X} {A} x) = Σᴰ.elementᴰ X A x
    elimHom (⊕elimE {X} {A} f) = Σᴰ.introᴰ X A (λ x → elimHom (f x))
    elimHom (⊕βE X A f x i) = ⊕βᴰ' X A f (λ y → elimHom (f y)) x i
    elimHom (⊕ηE X A g i) = ⊕ηᴰ' X A g (elimHom g) i
    -- indexed products
    elimHom (πE {X} {A} x) = Πᴰ.elementᴰ X A x
    elimHom (&introE {X} {A} f) = Πᴰ.introᴰ X A (λ x → elimHom (f x))
    elimHom (&βE X A f x i) = &βᴰ' X A f (λ y → elimHom (f y)) x i
    elimHom (&ηE X A g i) = &ηᴰ' X A g (elimHom g) i

    -- | The eliminator: a global section of the displayed model.
    elim : GlobalSection Cᴰ
    elim .F-obᴰ = elimOb
    elim .F-homᴰ = elimHom
    elim .F-idᴰ = refl
    elim .F-seqᴰ _ _ = refl
