{-# OPTIONS --lossy-unification #-}
{- The Kleene star in the "just sets" model is `List`.

   `A *` is the initial algebra of `X ↦ ε ⊕ (A ⊗ X)`, which under the
   set-valued reading is `X ↦ Unit ⊎ (A × X)`. So its initial algebra is
   `List ⟨ A ⟩`, `rec` is `foldr`, and uniqueness of folds is ordinary
   induction on lists.
-}
module Semantics.Instances.SetsInductive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool using (true; false)
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

import Semantics.Notation
import Semantics.Inductive.Functor
import Semantics.Inductive.Algebra
import Semantics.Inductive.KleeneStar

open import Semantics.Instances.Sets

module _ (ℓ : Level) (Gen : hSet ℓ) where
  private
    M = SetsOn ℓ Gen

  module N = Semantics.Notation M
  module SemF = Semantics.Inductive.Functor M
  module SemA = Semantics.Inductive.Algebra M
  module SemK = Semantics.Inductive.KleeneStar M

  module _ (A : hSet ℓ) where
    module S = SemK.Star A

    private
      L : hSet ℓ
      L = List ⟨ A ⟩ , isOfHLevelList 0 (A .snd)

      Carrier : Unit* {ℓ} → hSet ℓ
      Carrier _ = L

      rollL : ⟨ SemF.⟦ S.*Ty tt* ⟧ Carrier ⟩ → List ⟨ A ⟩
      rollL (lift true , _) = []
      rollL (lift false , (a , l)) = a ∷ l

      module _ (B : Unit* {ℓ} → hSet ℓ) (β : SemA.Algebra S.*Ty B) where
        recL : List ⟨ A ⟩ → ⟨ B tt* ⟩
        recL [] = β tt* (lift true , tt*)
        recL (a ∷ l) = β tt* (lift false , (a , recL l))

        homoL : SemA.isHomo S.*Ty (Carrier , λ _ → rollL) (B , β) (λ _ → recL)
        homoL u = funExt lem
          where
          lem : (x : ⟨ SemF.⟦ S.*Ty u ⟧ Carrier ⟩)
              → recL (rollL x) ≡ β u (SemF.map (S.*Ty u) (λ _ → recL) x)
          lem (lift true , _) = refl
          lem (lift false , _) = refl

        uniqL : (ϕ : SemA.AlgHom S.*Ty (Carrier , λ _ → rollL) (B , β))
              → ∀ l → recL l ≡ ϕ .fst tt* l
        uniqL ϕ [] = sym (funExt⁻ (ϕ .snd tt*) (lift true , tt*))
        uniqL ϕ (a ∷ l) =
          cong (λ z → β tt* (lift false , (a , z))) (uniqL ϕ l)
          ∙ sym (funExt⁻ (ϕ .snd tt*) (lift false , (a , l)))

    -- | `A *` exists in the sets model, and is `List ⟨ A ⟩`.
    ⋆InitSets : SemA.InitialAlgebra S.*Ty
    ⋆InitSets .fst = Carrier , λ _ → rollL
    ⋆InitSets .snd (B , β) .fst = (λ _ → recL B β) , homoL B β
    ⋆InitSets .snd (B , β) .snd ϕ =
      SemA.AlgHom≡ S.*Ty (funExt λ u → funExt (uniqL B β ϕ))
