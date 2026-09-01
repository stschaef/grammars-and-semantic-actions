{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A decision and a `Cover Bool (DecCover A)` are interchangeable
   (`Decidable/Base`): `total` is soundness + completeness, `disjoint` is
   consistency.  Exhibit a judgment as a CELL of a cover and `decideCell`
   gives the checker.  Not free: `total` IS completeness. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Combinator.Complete
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Bool using (Bool ; true ; false)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Cover.Base σeq V vs 𝒫 public
  using (Cover ; total ; disjoint ; cover-elim)
open import Theory.Type.Decidable.Base σeq V vs 𝒫 public
  using (Decidable ; DecTy ; ¬Ty ; dec-yes ; dec-no
        ; DecCover ; decisionCover ; coverDecidable ; dec-cover)
-- restated from `Route` rather than importing the routing module
DiscreteEq : {ℓY : Level} → Type ℓY → Type ℓY
DiscreteEq Y = (y y' : Y) → (y Eq.≡ y') Sum.⊎ ((y Eq.≡ y') → Empty.⊥)

private variable ℓA ℓY : Level

-- a decision IS a cover of `Bool`, both ways
module _ {s : S} {A : TheoryTy ℓA s} where

  asCover : Decidable A → Cover Bool (DecCover A)
  asCover = decisionCover

  fromCover : Cover Bool (DecCover A) → Decidable A
  fromCover = coverDecidable

-- the working direction: completeness lives in `total`, `disjoint`
-- refutes the cells not taken
decideCell : {s : S} {Y : Type ℓY} {Λ : Y → TheoryTy ℓA s}
  → DiscreteEq Y → Cover Y Λ → (y : Y) → Decidable (Λ y)
decideCell decY cov = dec-cover decY cov
