open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
import Cubical.Categories.LocallySmall.Category.Base as LS
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

import Theory.Free.Base as FB
module Theory.Type.Category
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS} {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'') (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP) where

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.HLevels σeq V vs 𝒫

open Σω
open Liftω

SetTheoryTy : (ℓA : Level) → S → Type _
SetTheoryTy ℓA s = Σ[ A ∈ TheoryTy ℓA s ] isSetTheoryTy A

SetTheoryTyω : S → Typeω
SetTheoryTyω s = Σω (Liftω Level) λ (liftω ℓA) → Liftω (SetTheoryTy ℓA s)

TheoryTyHomℓ : {s : S} → SetTheoryTyω s → SetTheoryTyω s → Level
TheoryTyHomℓ (liftω ℓA , liftω A) (liftω ℓB , liftω B) =
  ℓ-max ℓM (ℓ-max ℓA ℓB)

TheoryTyCat : (s : S) → LS.Category (SetTheoryTyω s) TheoryTyHomℓ
TheoryTyCat s .LS.Category.Hom[_,_] (liftω ℓA , liftω A) (liftω ℓB , liftω B) =
  A .fst ⊢ B .fst
TheoryTyCat s .LS.Category.id _ x = x
TheoryTyCat s .LS.Category._⋆_ f g m x = g m (f m x)
TheoryTyCat s .LS.Category.⋆IdL f = refl
TheoryTyCat s .LS.Category.⋆IdR f = refl
TheoryTyCat s .LS.Category.⋆Assoc f g h = refl
TheoryTyCat s .LS.Category.isSetHom {y = liftω ℓB , liftω B} =
  isSetΠ2 λ m x → B .snd m
