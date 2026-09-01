-- Used by `Theory/Type/Guarded/Justification`, for `Split` and `parts`.
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Code.Container
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Foundations.More
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥*)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
import Cubical.Data.Equality as Eq

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Lift.Base σeq V vs 𝒫
open import Theory.Type.Code.Base σeq V vs 𝒫

Split : (o : σ .ops) → ↓M (σ .resultSort o) → Type ℓM
Split o m = Σ[ ms ∈ interpIn o ↓M ] (op o ms Eq.≡ m)

parts : {o : σ .ops} {m : ↓M (σ .resultSort o)} → Split o m → interpIn o ↓M
parts sp = sp .fst

module _ {ℓA ℓX} {X : Type ℓX} {xs : X → S} where

  private
    ℓSh ℓPos : Level
    ℓSh = ℓA ⊔ℓ ℓX ⊔ℓ ℓM
    ℓPos = ℓX

  Ix : Type (ℓ-max ℓX ℓM)
  Ix = Σ[ x ∈ X ] ↓M (xs x)

  Sh : {s : S} → Functor ℓA X xs s → ↓M s → Type ℓSh
  Sh (k A) m = LiftTheoryTy ℓSh A m
  Sh (Var x) m = Unit*
  Sh (⊕e Y G) m = Σ[ y ∈ Y ] Sh (G y) m
  Sh (&e Y G) m = (y : Y) → Sh (G y) m
  Sh (G &e2 G') m = Sh G m × Sh G' m
  Sh (⊗e o G) m =
    Σ[ sp ∈ Split o m ] ((a : arities σ o) → Sh (G a) (parts sp a))

  Pos : {s : S} (F : Functor ℓA X xs s) (m : ↓M s) → Sh F m → Type ℓPos
  Pos (k A) m sh = ⊥*
  Pos (Var x) m sh = Unit*
  Pos (⊕e Y G) m (y , sh) = Pos (G y) m sh
  Pos (&e Y G) m sh = Σ[ y ∈ Y ] Pos (G y) m (sh y)
  Pos (G &e2 G') m (sh , sh') = Pos G m sh ⊎ Pos G' m sh'
  Pos (⊗e o G) m (sp , sh) = Σ[ a ∈ arities σ o ] Pos (G a) (parts sp a) (sh a)

  nx : {s : S} (F : Functor ℓA X xs s) (m : ↓M s) (sh : Sh F m)
     → Pos F m sh → Ix
  nx (Var x) m sh p = x , m
  nx (⊕e Y G) m (y , sh) p = nx (G y) m sh p
  nx (&e Y G) m sh (y , p) = nx (G y) m (sh y) p
  nx (G &e2 G') m (sh , sh') (inl p) = nx G m sh p
  nx (G &e2 G') m (sh , sh') (inr p) = nx G' m sh' p
  nx (⊗e o G) m (sp , sh) (a , p) = nx (G a) (parts sp a) (sh a) p
