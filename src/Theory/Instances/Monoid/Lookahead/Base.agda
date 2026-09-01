{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Lookahead.Base
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

import Cubical.Data.Empty as Empty
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using ([] ; _∷_ ; _++_ ; ++-assoc)
open import Cubical.Data.List.Properties using (¬cons≡nil ; cons-inj₁)
open import Cubical.Data.Unit using (tt ; tt*)
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Type.Cover.Base MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Decidable.Base MonEqns Alphabet (λ _ → tt) listPresentation

-- `ε₁` classifies the empty word, `tk c` every word beginning with `c`.
data M₁ : Type ℓAlph where
  ε₁ : M₁
  tk : Alphabet → M₁

-- The fibres of the classifying map Σ* ↠ M₁.
Λ₁ : M₁ → TheoryTy ℓAlph tt
Λ₁ ε₁     = LiftTheoryTy ℓAlph εTy
Λ₁ (tk c) = literal c ⊗ ⊤Ty

-- Disjointness is cons-injectivity: with the list presentation both sides
-- reduce on the nose, so no normal form intervenes.
Λ-disjoint : Disjoint Λ₁
Λ-disjoint ε₁ ε₁ neq = λ _ _ → Empty.rec (neq Eq.refl)
Λ-disjoint ε₁ (tk c) _ m (lift (_ , p , _) , (ms , q , (lc , _))) =
  Empty.rec (¬cons≡nil path)
  where
  path : c ∷ ms (suc zero) ≡ []
  path = cong (_++ ms (suc zero)) (sym (Eq.eqToPath lc))
       ∙ Eq.eqToPath q ∙ sym (Eq.eqToPath p)
Λ-disjoint (tk c) ε₁ _ m ((ms , q , (lc , _)) , lift (_ , p , _)) =
  Empty.rec (¬cons≡nil path)
  where
  path : c ∷ ms (suc zero) ≡ []
  path = cong (_++ ms (suc zero)) (sym (Eq.eqToPath lc))
       ∙ Eq.eqToPath q ∙ sym (Eq.eqToPath p)
Λ-disjoint (tk c) (tk c') neq m ((ms , q , (lc , _)) , (ns , r , (lc' , _))) =
  Empty.rec (neq (Eq.pathToEq (cong tk (cons-inj₁ path))))
  where
  path : c ∷ ms (suc zero) ≡ c' ∷ ns (suc zero)
  path = cong (_++ ms (suc zero)) (sym (Eq.eqToPath lc))
       ∙ Eq.eqToPath q ∙ sym (Eq.eqToPath r)
       ∙ cong (_++ ns (suc zero)) (Eq.eqToPath lc')

-- Structural recursion: every index equation is `Eq.refl`, so the dispatch
-- reduces on canonical inputs.
Λ-total : Total Λ₁
Λ-total [] _ = ε₁ , lift ((λ ()) , Eq.refl , tt*)
Λ-total (c ∷ cs) _ = tk c , (two (c ∷ []) cs , Eq.refl , (Eq.refl , (tt , tt*)))

lookaheadCover : Cover M₁ Λ₁
lookaheadCover .disjoint = Λ-disjoint
lookaheadCover .total = Λ-total

-- One token decides the unit: empty word, or disjointness refutes it.
private
  ε-branch : ∀ o → Λ₁ o ⊢ DecTy εTy
  ε-branch ε₁ = dec-yes ∘⊢ lowerTy
  ε-branch (tk c) =
    dec-no ∘⊢ ⇒-intro (Λ-disjoint (tk c) ε₁ (λ ()) ∘⊢ (id⊢ ,&p liftTy))

dec-ε : Decidable εTy
dec-ε = ⊕ᴰ-elim ε-branch ∘⊢ Λ-total
