{-# OPTIONS --lossy-unification --allow-unsolved-metas #-}
{- The associator, the pentagon, and the assembled displayed monoidal
   structure. See `Semantics.Displayed.ReindexMonoidal.Base` for the
   tensor, the structure maps, and the unitor coherences.
-}
module Semantics.Displayed.ReindexMonoidal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Monoidal.Functor
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.TotalCategory using (∫C)

open import Cubical.Categories.Displayed.Base
import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.Monoidal.Base
open import Cubical.Categories.Displayed.Instances.Reindex.Base using (reindex)
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration using (isFibration)

open import Semantics.Displayed.IsoLift
open import Semantics.Displayed.ReindexMonoidal.Base
open import Semantics.Displayed.ReindexMonoidal.Assoc

private
  variable
    ℓM ℓM' ℓN ℓN' ℓCᴰ ℓCᴰ' : Level

open Functor
open Functorᴰ
open NatTrans
open NatIso
open NatIsoᴰ
open NatTransᴰ
open isIso
open isIsoᴰ

module _ {M : MonoidalCategory ℓM ℓM'} {N : MonoidalCategory ℓN ℓN'}
  {Cᴰ : Categoryᴰ (MonoidalCategory.C N) ℓCᴰ ℓCᴰ'}
  (P : MonoidalStrᴰ N Cᴰ)
  (G : StrongMonoidalFunctor M N)
  (cartLifts : isFibration Cᴰ)
  where
  private
    module M = MonoidalCategory M
    module N = MonoidalCategory N
    module Cᴰ = Fibers Cᴰ
    module R = HomᴰReasoning Cᴰ
    module P = MonoidalStrᴰ P
    module G = StrongMonoidalFunctor G
    Rᴰ : Categoryᴰ M.C ℓCᴰ ℓCᴰ'
    Rᴰ = reindex Cᴰ G.F

    module Rᴰ = Fibers Rᴰ

  open Assoc P G cartLifts public

  open MonoidalStrᴰ

  reindexMonoidalStrᴰ : MonoidalStrᴰ M Rᴰ
  reindexMonoidalStrᴰ .tenstrᴰ = tenstrᴰ'
  reindexMonoidalStrᴰ .αᴰ .transᴰ .N-obᴰ (xᴰ , (yᴰ , zᴰ)) = αᴰ'⟨ xᴰ , yᴰ , zᴰ ⟩
  reindexMonoidalStrᴰ .αᴰ .transᴰ .N-homᴰ (fᴰ , (gᴰ , hᴰ)) = α'-nat fᴰ gᴰ hᴰ
  reindexMonoidalStrᴰ .αᴰ .nIsoᴰ (xᴰ , (yᴰ , zᴰ)) .invᴰ = α⁻¹ᴰ'⟨ xᴰ , yᴰ , zᴰ ⟩
  reindexMonoidalStrᴰ .αᴰ .nIsoᴰ (xᴰ , (yᴰ , zᴰ)) .secᴰ = α'-sec xᴰ yᴰ zᴰ
  reindexMonoidalStrᴰ .αᴰ .nIsoᴰ (xᴰ , (yᴰ , zᴰ)) .retᴰ = α'-ret xᴰ yᴰ zᴰ
  reindexMonoidalStrᴰ .ηᴰ .transᴰ .N-obᴰ xᴰ = ηᴰ'⟨ xᴰ ⟩
  reindexMonoidalStrᴰ .ηᴰ .transᴰ .N-homᴰ fᴰ = η'-nat fᴰ
  reindexMonoidalStrᴰ .ηᴰ .nIsoᴰ xᴰ .invᴰ = η⁻¹ᴰ'⟨ xᴰ ⟩
  reindexMonoidalStrᴰ .ηᴰ .nIsoᴰ xᴰ .secᴰ = η'-sec xᴰ
  reindexMonoidalStrᴰ .ηᴰ .nIsoᴰ xᴰ .retᴰ = η'-ret xᴰ
  reindexMonoidalStrᴰ .ρᴰ .transᴰ .N-obᴰ xᴰ = ρᴰ'⟨ xᴰ ⟩
  reindexMonoidalStrᴰ .ρᴰ .transᴰ .N-homᴰ fᴰ = ρ'-nat fᴰ
  reindexMonoidalStrᴰ .ρᴰ .nIsoᴰ xᴰ .invᴰ = ρ⁻¹ᴰ'⟨ xᴰ ⟩
  reindexMonoidalStrᴰ .ρᴰ .nIsoᴰ xᴰ .secᴰ = ρ'-sec xᴰ
  reindexMonoidalStrᴰ .ρᴰ .nIsoᴰ xᴰ .retᴰ = ρ'-ret xᴰ
  reindexMonoidalStrᴰ .pentagonᴰ wᴰ xᴰ yᴰ zᴰ = {!!}
  reindexMonoidalStrᴰ .triangleᴰ xᴰ yᴰ = triangleᴰ' xᴰ yᴰ
