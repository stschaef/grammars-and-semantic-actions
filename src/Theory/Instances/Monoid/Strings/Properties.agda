{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Instances.Monoid.Strings.Properties
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
open import Theory.Instances.Monoid.Strings.HLevels Alphabet isSetAlphabet

open WildCatNotation
open WildCatIso

⊗-map-∘ : {A B C D E F : TheoryTy ℓM tt}
  (f : C ⊢ E) (g : D ⊢ F) (f' : A ⊢ C) (g' : B ⊢ D)
  → ⊗-map f g ∘⊢ ⊗-map f' g' ≡ ⊗-map (f ∘⊢ f') (g ∘⊢ g')
⊗-map-∘ f g f' g' = refl

transportEq-nat : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} (f : A ⊢ B)
  {x y : String} (q : x Eq.≡ y) (a : A x)
  → f y (Eq.transport A q a) ≡ Eq.transport B q (f x a)
transportEq-nat f Eq.refl a = refl

⊗-unit-l-nat : {K L : TheoryTy ℓM tt} (f : K ⊢ L)
  → f ∘⊢ ⊗-unit-l {A = K}
    ≡ ⊗-unit-l {A = L} ∘⊢ ⊗-map (id⊢ {A = εTy}) f
⊗-unit-l-nat f = funExt λ m → funExt λ where
  (ms , e , (u , (a , _))) →
    transportEq-nat f (Eq.pathToEq (unit-lPath ms u e)) a

⊗-assoc⁻-nat : {A B K L : TheoryTy ℓM tt} (f : K ⊢ L)
  → ⊗-assoc⁻ {A = A} {B = B} {C = L}
      ∘⊢ ⊗-map (id⊢ {A = A}) (⊗-map (id⊢ {A = B}) f)
    ≡ ⊗-map (id⊢ {A = A ⊗ B}) f ∘⊢ ⊗-assoc⁻ {A = A} {B = B} {C = K}
⊗-assoc⁻-nat f = refl

⊗-assoc-nat : {A B K L : TheoryTy ℓM tt} (f : K ⊢ L)
  → ⊗-map (id⊢ {A = A}) (⊗-map (id⊢ {A = B}) f)
      ∘⊢ ⊗-assoc {A = A} {B = B} {C = K}
    ≡ ⊗-assoc {A = A} {B = B} {C = L} ∘⊢ ⊗-map (id⊢ {A = A ⊗ B}) f
⊗-assoc-nat f = refl

module _ {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  {K : TheoryTy ℓD tt} where

  private
    pentL : A ⊗ B ⊗ C ⊗ K ⊢ (A ⊗ B ⊗ C) ⊗ K
    pentL = ⊗-map (⊗-assoc {A = A} {B = B} {C = C}) (id⊢ {A = K})
      ∘⊢ ⊗-assoc⁻ {A = A ⊗ B} {B = C} {C = K}
      ∘⊢ ⊗-assoc⁻ {A = A} {B = B} {C = C ⊗ K}

    pentR : A ⊗ B ⊗ C ⊗ K ⊢ (A ⊗ B ⊗ C) ⊗ K
    pentR = ⊗-assoc⁻ {A = A} {B = B ⊗ C} {C = K}
      ∘⊢ ⊗-map (id⊢ {A = A}) (⊗-assoc⁻ {A = B} {B = C} {C = K})

    pent⁻L : (A ⊗ B ⊗ C) ⊗ K ⊢ A ⊗ B ⊗ C ⊗ K
    pent⁻L = ⊗-assoc {A = A} {B = B} {C = C ⊗ K}
      ∘⊢ ⊗-assoc {A = A ⊗ B} {B = C} {C = K}
      ∘⊢ ⊗-map (⊗-assoc⁻ {A = A} {B = B} {C = C}) (id⊢ {A = K})

    pent⁻R : (A ⊗ B ⊗ C) ⊗ K ⊢ A ⊗ B ⊗ C ⊗ K
    pent⁻R = ⊗-map (id⊢ {A = A}) (⊗-assoc {A = B} {B = C} {C = K})
      ∘⊢ ⊗-assoc {A = A} {B = B ⊗ C} {C = K}

  ⊗-pent : pentL ≡ pentR
  ⊗-pent = funExt λ m → funExt (go m)
    where
    go : (m : String) (x : (A ⊗ B ⊗ C ⊗ K) m) → pentL m x ≡ pentR m x
    go m (ms , e , (a , ((ns , f , (b , ((ps , g , (c , (k' , _))) , _))) , _))) =
      ⊗PathP' {A = A ⊗ B ⊗ C} {B = K} refl (two≡ assoc3 refl)
        (⊗PathP' {A = A} {B = B ⊗ C} assoc3 refl refl refl) refl
      where
      assoc3 : (ms zero ++ ns zero) ++ ps zero ≡ ms zero ++ (ns zero ++ ps zero)
      assoc3 = ++-assoc (ms zero) (ns zero) (ps zero)

  ⊗-pent⁻ : pent⁻L ≡ pent⁻R
  ⊗-pent⁻ = funExt λ m → funExt (go m)
    where
    go : (m : String) (x : ((A ⊗ B ⊗ C) ⊗ K) m) → pent⁻L m x ≡ pent⁻R m x
    go m (ms , e , ((ns , f , (a , ((ps , g , (b , (c , _))) , _))) , (k' , _))) =
      ⊗PathP' {A = A} {B = B ⊗ C ⊗ K} refl (two≡ refl assoc3) refl
        (⊗PathP' {A = B} {B = C ⊗ K} assoc3 refl refl refl)
      where
      assoc3 : ps zero ++ (ps (suc zero) ++ ms (suc zero))
             ≡ ns (suc zero) ++ ms (suc zero)
      assoc3 = sym (++-assoc (ps zero) (ps (suc zero)) (ms (suc zero)))
             ∙ cong (_++ ms (suc zero)) (Eq.eqToPath g)
