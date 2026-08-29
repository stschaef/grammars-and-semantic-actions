{-# OPTIONS --lossy-unification #-}
{- Weakening a model to a displayed model.

   Any model `M` is a displayed model over any other model `N` with the
   same index level, with constant fibres. A section of it is exactly a
   structure-preserving map `N → M`, so the recursor is the eliminator
   applied to a weakening — no second induction over the syntax.

   Every displayed universal element here is the target's own universal
   element, following the pattern of ccl's
   `Displayed/Instances/Weaken/UncurriedProperties`.
-}
module Semantics.Displayed.Weaken where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Categories.Category
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Limits.IndexedProduct.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Displayed.Monoidal.Base
import Cubical.Categories.Displayed.Instances.Weaken.Base as Wk
import Cubical.Categories.Displayed.Instances.Weaken.Monoidal as WkMon
open import Cubical.Foundations.Equiv.Dependent

open import Semantics.Model
open import Semantics.Displayed.Model
open import Semantics.Structure.Biclosed
open import Semantics.Structure.IndexedCoproduct
open import Semantics.Displayed.IndexedProduct

open UniversalElement
open isIsoOver
open MonoidalCategoryᴰ

module _ {ℓ ℓ' ℓX ℓ₂ ℓ₂'} (N : Model ℓ ℓ' ℓX) (M : Model ℓ₂ ℓ₂' ℓX) where
  private
    module N = Model N
    module M = Model M
    module wkD = Fibers (Wk.weaken N.C M.C)
    module Mbc = Biclosed M.biclosed

  weakenModel : Modelᴰ N ℓ₂ ℓ₂'
  weakenModel .Modelᴰ.Cᴰ = Wk.weaken N.C M.C
  weakenModel .Modelᴰ.MCᴰ = WkMon.weaken N.MC M.MC .monstrᴰ
  weakenModel .Modelᴰ.biclosedᴰ .Biclosedᴰ.⊸uesᴰ Bᴰ Dᴰ = ue
    where
    ueM = Mbc.⊸ues Bᴰ Dᴰ
    module ueM = UniversalElementNotation ueM
    ue = ueM .vertex
       , ueM .element
       , λ Γ Γᴰ → record
         { inv = λ _ p → ueM.intro p
         ; rightInv = λ _ _ →
             (wkD.rectifyOut {e' = refl} $ wkD.reind-filler⁻ _) ∙ ueM.β
         ; leftInv = λ _ _ → ueM.intro≡ $
             wkD.rectifyOut {e' = refl} $ wkD.reind-filler⁻ _ }
  weakenModel .Modelᴰ.biclosedᴰ .Biclosedᴰ.⟜uesᴰ Aᴰ Dᴰ = ue
    where
    ueM = Mbc.⟜ues Aᴰ Dᴰ
    module ueM = UniversalElementNotation ueM
    ue = ueM .vertex
       , ueM .element
       , λ Γ Γᴰ → record
         { inv = λ _ p → ueM.intro p
         ; rightInv = λ _ _ →
             (wkD.rectifyOut {e' = refl} $ wkD.reind-filler⁻ _) ∙ ueM.β
         ; leftInv = λ _ _ → ueM.intro≡ $
             wkD.rectifyOut {e' = refl} $ wkD.reind-filler⁻ _ }
  weakenModel .Modelᴰ.Πsᴰ X A Aᴰ = ue
    where
    ueM = M.Πs X Aᴰ
    module ueM = UniversalElementNotation ueM
    ue = ueM .vertex
       , ueM .element
       , λ Γ Γᴰ → record
         { inv = λ _ p → ueM.intro p
         ; rightInv = λ _ _ → funExt λ x →
             (wkD.rectifyOut {e' = refl} $ wkD.reind-filler⁻ _)
             ∙ funExt⁻ ueM.β x
         ; leftInv = λ _ _ → ueM.intro≡ $ funExt λ x →
             wkD.rectifyOut {e' = refl} $ wkD.reind-filler⁻ _ }
  weakenModel .Modelᴰ.Σsᴰ X A Aᴰ = ue
    where
    ueM = M.Σs X Aᴰ
    module ueM = UniversalElementNotation ueM
    ue = ueM .vertex
       , ueM .element
       , λ Γ Γᴰ → record
         { inv = λ _ p → ueM.intro p
         ; rightInv = λ _ _ → funExt λ x →
             (wkD.rectifyOut {e' = refl} $ wkD.reind-filler⁻ _)
             ∙ funExt⁻ ueM.β x
         ; leftInv = λ _ _ → ueM.intro≡ $ funExt λ x →
             wkD.rectifyOut {e' = refl} $ wkD.reind-filler⁻ _ }
