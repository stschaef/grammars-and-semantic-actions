open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
import Cubical.Algebra.Theory.Finitary.Free.Closing as Cl
import Cubical.Data.Equality as Eq
open Category
open SortedSig
open SortedEqns
module Theory.Free.Closing
  {ℓ ℓ'' ℓv ℓS} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  where

open import Theory.Free.Base σeq V vs

-- The quotiented terms is the canonical presentation of the free model
closingPresentation : FreePresentation (Cl.ℓClosing ℓS ℓ ℓ'' ℓv)
closingPresentation .P = Cl.FreeOb σeq V vs
closingPresentation .satStrict e ρ = Eq.pathToEq (Cl.FreeOb σeq V vs .snd .snd e ρ)
closingPresentation .gen v = Cl.gen σeq V vs v
closingPresentation .rec isSetX α sat ρ = Cl.rec σeq isSetX α sat ρ
closingPresentation .recGen isSetX α sat ρ v = refl
closingPresentation .recOp isSetX α sat ρ o ms = refl
closingPresentation .recUniq isSetX α sat ρ f homf fβ m =
  Cl.recUniq σeq isSetX α sat ρ f
    (λ o x y eq → cong (f (σ .resultSort o)) eq ∙ homf o x)
    fβ m
