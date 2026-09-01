{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Instances.Monoid.Strings.Distributivity
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

⊗⊕-distL : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → (A ⊕ B) ⊗ C ⊢ (A ⊗ C) ⊕ (B ⊗ C)
⊗⊕-distL m (ms , e , (Sum.inl a , r)) = Sum.inl (ms , e , (a , r))
⊗⊕-distL m (ms , e , (Sum.inr b , r)) = Sum.inr (ms , e , (b , r))

⊗⊕-distR : {ℓA ℓB ℓC : Level} {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  {C : TheoryTy ℓC tt} → A ⊗ (B ⊕ C) ⊢ (A ⊗ B) ⊕ (A ⊗ C)
⊗⊕-distR {ℓA = ℓA} {ℓB = ℓB} {ℓC = ℓC} {A = A} {B = B} {C = C} =
  ⊗-elim {ℓs = two ℓA (ℓ-max ℓB ℓC)} (A , B ⊕ C , tt*)
    {C = (A ⊗ B) ⊕ (A ⊗ C)} λ where
    {ms} (a , Sum.inl b , _) →
      Sum.inl (⊗-intro {ℓs = two ℓA ℓB} (A , B , tt*) ms (a , b , tt*))
    {ms} (a , Sum.inr c , _) →
      Sum.inr (⊗-intro {ℓs = two ℓA ℓC} (A , C , tt*) ms (a , c , tt*))

⊗⊥-annihL : {C : TheoryTy ℓC tt} → ⊥Ty ⊗ C ⊢ ⊥Ty
⊗⊥-annihL m (ms , e , (b , _)) = b

⊗⊥-annihR : {C : TheoryTy ℓC tt} → C ⊗ ⊥Ty ⊢ ⊥Ty
⊗⊥-annihR m (ms , e , (_ , (b , _))) = b
