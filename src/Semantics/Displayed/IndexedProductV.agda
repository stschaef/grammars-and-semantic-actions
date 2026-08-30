{-# OPTIONS --lossy-unification #-}
{- Vertical set-indexed products and coproducts.

   `Presheafⱽ x Cᴰ` is `Presheafᴰ (C [-, x ]) Cᴰ`, i.e. a presheaf
   on `Cᴰ / (C [-, x ])`. For a *fixed* base object all components
   of an indexed family live on that same category, so unlike the
   displayed case (`Semantics.Displayed.IndexedProduct`) there is
   nothing to reindex: the vertical indexed product is ccl's
   ordinary `ΠTyPsh`, unchanged.

   Vertical is the notion that survives reindexing along an
   arbitrary functor, which is what `elimLocal` needs — see
   ccl's `Displayed/Limits/{Terminal,BinProduct}` for the terminal
   and binary cases this generalises.
-}
module Semantics.Displayed.IndexedProductV where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets using (_[-,_])
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.IndexedProduct
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Limits.IndexedProduct.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Instances.Reindex.Base using (reindex)
open import Cubical.Categories.Displayed.Instances.Reindex.UniversalProperties
  using (reindex-π-/; reindexRepresentableIsoⱽ; reindexReflectsUMPⱽ)
open import Cubical.Categories.Presheaf.Constructions.Reindex

open import Semantics.Structure.IndexedCoproduct using (ΣTy)
open import Semantics.Displayed.IndexedProduct using (ΠTyPshᴰ; ΠTyᴰ; ΣTyᴰ)

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓ ℓP ℓQ ℓPᴰ : Level

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  {c : Category.ob C} where

  -- | The vertical indexed product of displayed presheaves. All
  --   components are presheaves on the same category, so this is
  --   just the ordinary one.
  ΠTyPshⱽ : {X : Type ℓ} → (X → Presheafⱽ c Cᴰ ℓPᴰ)
          → Presheafⱽ c Cᴰ (ℓ-max ℓ ℓPᴰ)
  ΠTyPshⱽ = ΠTyPsh

  -- | A vertical set-indexed product: fibrewise, over the identity.
  --   Stated as a `Representableⱽ`, as ccl states `BinProductⱽ`, so
  --   that ccl's `◁PshIsoⱽ` machinery applies directly.
  ΠTyⱽ : {X : Type ℓ} (Aⱽ : X → Categoryᴰ.ob[_] Cᴰ c) → Type _
  ΠTyⱽ Aⱽ = Representableⱽ Cᴰ c (ΠTyPshⱽ (λ x → Cᴰ [-][-, Aⱽ x ]))

  -- | The usual way to build one: give the vertex, the projections,
  --   and the universal property.
  mkΠTyⱽ : {X : Type ℓ} {Aⱽ : X → Categoryᴰ.ob[_] Cᴰ c}
    → UniversalElementⱽ' Cᴰ c (ΠTyPshⱽ (λ x → Cᴰ [-][-, Aⱽ x ]))
    → ΠTyⱽ Aⱽ
  mkΠTyⱽ = UniversalElementⱽ'.REPRⱽ

-- | Vertical coproducts are the ^op dual, as in the displayed case.
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  {c : Category.ob C} where

  ΣTyⱽ : {X : Type ℓ} (Aⱽ : X → Categoryᴰ.ob[_] Cᴰ c) → Type _
  ΣTyⱽ = ΠTyⱽ (Cᴰ ^opᴰ) {c}

------------------------------------------------------------------------
-- Indexed products of presheaves are functorial in isomorphisms
------------------------------------------------------------------------

module _ {C : Category ℓC ℓC'} {X : Type ℓ}
  {P⟨x⟩ : X → Presheaf C ℓP} {Q⟨x⟩ : X → Presheaf C ℓQ}
  (isos : ∀ x → PshIso (P⟨x⟩ x) (Q⟨x⟩ x))
  where
  open PshIso
  open PshHom

  ΠTyPshIso : PshIso (ΠTyPsh P⟨x⟩) (ΠTyPsh Q⟨x⟩)
  ΠTyPshIso = Isos→PshIso
    (λ c → iso (λ p x → isos x .trans .N-ob c (p x))
               (λ q x → isos x .nIso c .fst (q x))
               (λ q → funExt (λ x → isos x .nIso c .snd .fst (q x)))
               (λ p → funExt (λ x → isos x .nIso c .snd .snd (p x))))
    (λ c c' f p → funExt (λ x → isos x .trans .N-hom c c' f (p x)))

------------------------------------------------------------------------
-- Vertical indexed products become displayed ones
--
-- The indexed analogue of ccl's `BinProductⱽ→ᴰ` / `BinProductⱽ+π*→ᴰ`.
-- Unlike `ΠTyPshⱽ` and `ΣTyⱽ`, this one has real content: it is where
-- the fibration structure of a `Modelⱽ` gets used, to pull each `Aᴰ x`
-- back along the projection `π x` so the whole family lives over a
-- single base object.
------------------------------------------------------------------------

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  {X : Type ℓ} {A : X → Category.ob C}
  where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  open UniversalElement
  open PshIso

  -- | The fibrewise spec: the indexed product of the reindexings of
  --   each `Cᴰ [-][-, Aᴰ x ]` along the projection `π x`.
  ΠTyᴰ'Spec : (Π : ΠTy C A) (Aᴰ : ∀ x → Cᴰ.ob[ A x ])
    → Presheafⱽ (Π .vertex) Cᴰ (ℓ-max ℓ ℓCᴰ')
  ΠTyᴰ'Spec Π Aᴰ = ΠTyPsh
    (λ x → CartesianLiftPshSpec (C [-, A x ]) Cᴰ (Cᴰ [-][-, Aᴰ x ]) (Π .element x))

  ΠTyᴰ' : (Π : ΠTy C A) (Aᴰ : ∀ x → Cᴰ.ob[ A x ]) → Type _
  ΠTyᴰ' Π Aᴰ = Representableⱽ Cᴰ (Π .vertex) (ΠTyᴰ'Spec Π Aᴰ)

  -- | The two specs agree pointwise; only the actions differ, by a
  --   reindexing.
  ΠTyᴰ'Spec≅ΠTyᴰSpec : (Π : ΠTy C A) (Aᴰ : ∀ x → Cᴰ.ob[ A x ])
    → FiberwisePshIsoᴰ (yoRec (ΠTyPsh (λ x → C [-, A x ])) (Π .element))
        (ΠTyᴰ'Spec Π Aᴰ)
        (ΠTyPshᴰ Cᴰ (λ x → Cᴰ [-][-, Aᴰ x ]))
  ΠTyᴰ'Spec≅ΠTyᴰSpec Π Aᴰ = Isos→PshIso (λ _ → idIso) (λ _ _ _ _ → funExt (λ x →
    Cᴰ.rectifyOut (Cᴰ.reind-filler⁻ _ ∙ Cᴰ.reind-filler _)))

  ΠTyⱽ→ᴰ : (Π : ΠTy C A) (Aᴰ : ∀ x → Cᴰ.ob[ A x ])
    → ΠTyᴰ' Π Aᴰ → ΠTyᴰ Cᴰ Aᴰ Π
  ΠTyⱽ→ᴰ Π Aᴰ (ΠAᴰ , repr) =
    Representableⱽ→UniversalElementᴰ Cᴰ (ΠTyPsh (λ x → C [-, A x ]))
      (ΠTyPshᴰ Cᴰ (λ x → Cᴰ [-][-, Aᴰ x ])) Π
      (ΠAᴰ , (repr ⋆PshIso ΠTyᴰ'Spec≅ΠTyᴰSpec Π Aᴰ))

  -- | The form actually used: a *vertical* indexed product of the
  --   cartesian lifts of the family along the projections is a
  --   displayed indexed product over the base one.
  ΠTyⱽ+π*→ᴰ : (Π : ΠTy C A) (Aᴰ : ∀ x → Cᴰ.ob[ A x ])
    → (π*Aᴰ : ∀ x → CartesianLift Cᴰ (Π .element x) (Aᴰ x))
    → ΠTyⱽ Cᴰ (λ x → π*Aᴰ x .fst)
    → ΠTyᴰ Cᴰ Aᴰ Π
  ΠTyⱽ+π*→ᴰ Π Aᴰ π*Aᴰ Πⱽ = ΠTyⱽ→ᴰ Π Aᴰ
    (Πⱽ ◁PshIsoⱽ ΠTyPshIso (λ x → π*Aᴰ x .snd))

-- | Coproducts are the ^op dual, exactly as `BinCoproductⱽ→ᴰ` is
--   `BinProductⱽ→ᴰ` in the opposite displayed category.
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  {X : Type ℓ} {A : X → Category.ob C}
  where
  ΣTyⱽ+π*→ᴰ : (Σ' : ΣTy C A) (Aᴰ : ∀ x → Categoryᴰ.ob[_] Cᴰ (A x))
    → (σ*Aᴰ : ∀ x → CartesianLift (Cᴰ ^opᴰ) (UniversalElement.element Σ' x) (Aᴰ x))
    → ΣTyⱽ Cᴰ (λ x → σ*Aᴰ x .fst)
    → ΣTyᴰ Cᴰ Aᴰ Σ'
  ΣTyⱽ+π*→ᴰ = ΠTyⱽ+π*→ᴰ (Cᴰ ^opᴰ)

------------------------------------------------------------------------
-- Vertical indexed products survive reindexing along any functor
--
-- This is the point of the vertical formulation, and the reason
-- `elimLocal` can ask its caller for fibrewise data: unlike a
-- displayed monoidal structure, which needs a monoidal functor,
-- `ΠTyⱽ` and `ΣTyⱽ` transport along an arbitrary `F`.
------------------------------------------------------------------------

module _ {C : Category ℓC ℓC'} {E : Category ℓD ℓD'} (G : Functor E C)
  {X : Type ℓ} (P⟨x⟩ : X → Presheaf C ℓP)
  where
  -- | Reindexing commutes with indexed products of presheaves: both
  --   sides are `∀ x → P⟨x⟩ x (G c)` on the nose.
  reindΠTyPshIso : PshIso (reindPsh G (ΠTyPsh P⟨x⟩)) (ΠTyPsh (λ x → reindPsh G (P⟨x⟩ x)))
  reindΠTyPshIso = Isos→PshIso (λ _ → idIso) (λ _ _ _ _ → refl)

module _ {B : Category ℓB ℓB'} {D : Category ℓD ℓD'}
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ') (F : Functor B D)
  {c : Category.ob B} {X : Type ℓ}
  (Aⱽ : X → Categoryᴰ.ob[_] Dᴰ (Functor.F-ob F c))
  where

  ΠTyⱽReindex : ΠTyⱽ Dᴰ Aⱽ → ΠTyⱽ (reindex Dᴰ F) Aⱽ
  ΠTyⱽReindex Πⱽ =
    reindexReflectsUMPⱽ Dᴰ F c _ Πⱽ
    ◁PshIsoⱽ (reindΠTyPshIso (reindex-π-/ Dᴰ F c) (λ x → Dᴰ [-][-, Aⱽ x ])
             ⋆PshIso ΠTyPshIso (λ x → invPshIso (reindexRepresentableIsoⱽ Dᴰ F c (Aⱽ x))))

module _ {B : Category ℓB ℓB'} {D : Category ℓD ℓD'}
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ') (F : Functor B D)
  {c : Category.ob B} {X : Type ℓ}
  (Aⱽ : X → Categoryᴰ.ob[_] Dᴰ (Functor.F-ob F c))
  where

  private
    open Functor
    -- `_^opF` factors through `toOpOp`, so `reindex (Dᴰ ^opᴰ) (F ^opF)`
    -- does not even have the same *composition* as `(reindex Dᴰ F) ^opᴰ`.
    -- This op-functor does.
    opFᵈ : Functor (B ^op) (D ^op)
    opFᵈ .F-ob = F .F-ob
    opFᵈ .F-hom = F .F-hom
    opFᵈ .F-id = F .F-id
    opFᵈ .F-seq f g = F .F-seq g f

  -- | Reindexing an opposite is the opposite of the reindexing: with
  --   `opFᵈ` the objects, homs, identities and composites agree on the
  --   nose, and the remaining fields are proofs in a set.
  reindex^opᴰ : reindex (Dᴰ ^opᴰ) opFᵈ ≡ (reindex Dᴰ F) ^opᴰ
  reindex^opᴰ i .Categoryᴰ.ob[_] = Categoryᴰ.ob[_] (reindex (Dᴰ ^opᴰ) opFᵈ)
  reindex^opᴰ i .Categoryᴰ.Hom[_][_,_] = Categoryᴰ.Hom[_][_,_] (reindex (Dᴰ ^opᴰ) opFᵈ)
  reindex^opᴰ i .Categoryᴰ.idᴰ = Categoryᴰ.idᴰ (reindex (Dᴰ ^opᴰ) opFᵈ)
  reindex^opᴰ i .Categoryᴰ._⋆ᴰ_ = Categoryᴰ._⋆ᴰ_ (reindex (Dᴰ ^opᴰ) opFᵈ)
  reindex^opᴰ i .Categoryᴰ.isSetHomᴰ = Categoryᴰ.isSetHomᴰ (reindex (Dᴰ ^opᴰ) opFᵈ)
  reindex^opᴰ i .Categoryᴰ.⋆IdLᴰ fᴰ =
    isSet→SquareP (λ _ _ → Categoryᴰ.isSetHomᴰ Dᴰ)
      (Categoryᴰ.⋆IdLᴰ (reindex (Dᴰ ^opᴰ) opFᵈ) fᴰ)
      (Categoryᴰ.⋆IdLᴰ ((reindex Dᴰ F) ^opᴰ) fᴰ)
      refl refl i
  reindex^opᴰ i .Categoryᴰ.⋆IdRᴰ fᴰ =
    isSet→SquareP (λ _ _ → Categoryᴰ.isSetHomᴰ Dᴰ)
      (Categoryᴰ.⋆IdRᴰ (reindex (Dᴰ ^opᴰ) opFᵈ) fᴰ)
      (Categoryᴰ.⋆IdRᴰ ((reindex Dᴰ F) ^opᴰ) fᴰ)
      refl refl i
  reindex^opᴰ i .Categoryᴰ.⋆Assocᴰ fᴰ gᴰ hᴰ =
    isSet→SquareP (λ _ _ → Categoryᴰ.isSetHomᴰ Dᴰ)
      (Categoryᴰ.⋆Assocᴰ (reindex (Dᴰ ^opᴰ) opFᵈ) fᴰ gᴰ hᴰ)
      (Categoryᴰ.⋆Assocᴰ ((reindex Dᴰ F) ^opᴰ) fᴰ gᴰ hᴰ)
      refl refl i

  ΣTyⱽReindex : ΣTyⱽ Dᴰ Aⱽ → ΣTyⱽ (reindex Dᴰ F) Aⱽ
  ΣTyⱽReindex Σⱽ =
    transport (λ i → ΠTyⱽ (reindex^opᴰ i) Aⱽ)
      (ΠTyⱽReindex (Dᴰ ^opᴰ) opFᵈ Aⱽ Σⱽ)
