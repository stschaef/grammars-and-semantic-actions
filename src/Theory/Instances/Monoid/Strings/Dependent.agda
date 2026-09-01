{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Instances.Monoid.Strings.Dependent
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

private variable ℓA ℓB ℓC ℓD ℓY : Level

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Unit using (Unit ; tt ; Unit* ; tt*)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; ++-assoc ; ++-unit-r)
import Cubical.Data.List as L
import Cubical.Data.Empty as Emp
import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq
open import Cubical.Data.Equality.More using (isSet→isSetEq)

open import Cubical.WildCat.LocallySmall.Base

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings.Base Alphabet isSetAlphabet
open import Theory.Type.HLevels MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Inductive.HLevels MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Top.Properties MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Instances.Monoid.Strings.LinearProduct Alphabet isSetAlphabet

Dep : TheoryTy ℓA tt → (ℓB : Level) → Type _
Dep A ℓB = (l : String) → A l → TheoryTy ℓB tt

⊗ᴰ : (A : TheoryTy ℓA tt) → Dep A ℓB → TheoryTy (ℓ-max ℓM (sup 2 (two ℓA ℓB))) tt
⊗ᴰ A B m =
  Σ[ ms ∈ interpIn _⊙_ ↓M ]
    (op _⊙_ ms Eq.≡ m)
    × (Σ[ a ∈ A (ms zero) ] (B (ms zero) a (ms (suc zero)) × Unit* {ℓ-zero}))

⊗ᴰ-const : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → ⊗ᴰ A (λ _ _ → B) ≡ A ⊗ B
⊗ᴰ-const = refl

⊗ᴰ-assoc⁻ : {A : TheoryTy ℓA tt} {B : String → TheoryTy ℓB tt}
  {C : String → TheoryTy ℓC tt}
  → ⊗ᴰ A (λ l₁ _ → ⊗ᴰ (B l₁) (λ l₂ _ → C (l₁ ++ l₂)))
  ⊢ ⊗ᴰ (⊗ᴰ A (λ l _ → B l)) (λ l _ → C l)
⊗ᴰ-assoc⁻ m (ms , e , (a , ((ns , f , (b , (c , _))) , _))) =
  two (ms zero ++ ns zero) (ns (suc zero))
    , split
    , ((two (ms zero) (ns zero) , Eq.refl , (a , (b , tt*))) , (c , tt*))
  where
  split : ((ms zero ++ ns zero) ++ ns (suc zero)) Eq.≡ m
  split = ++-assocEq (ms zero) (ns zero) (ns (suc zero))
     Eq.∙ (Eq.ap (ms zero ++_) f Eq.∙ e)

