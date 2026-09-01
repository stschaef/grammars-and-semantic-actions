{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Instances.Monoid.Strings.LinearProduct
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

open WildCatNotation
open WildCatIso

-- in `Eq`: splittings must reduce to `Eq.refl` on canonical strings — a `pathToEq`
-- is stuck, and a stuck cast at `μ` blocks every recursor underneath it
++-assocEq : (a b c : String) → ((a ++ b) ++ c) Eq.≡ (a ++ (b ++ c))
++-assocEq [] b c = Eq.refl
++-assocEq (x ∷ a) b c = Eq.ap (x ∷_) (++-assocEq a b c)

++-unit-rEq : (a : String) → (a ++ []) Eq.≡ a
++-unit-rEq [] = Eq.refl
++-unit-rEq (x ∷ a) = Eq.ap (x ∷_) (++-unit-rEq a)

infixr 20 _⊗_

_⊗_ : TheoryTy ℓA tt → TheoryTy ℓB tt → TheoryTy _ tt
_⊗_ {ℓA = ℓA} {ℓB = ℓB} A B =
  ⊗[ _⊙_ ][ two ℓA ℓB ] (A , B , tt*)

⊗-map : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
        {C : TheoryTy ℓC tt} {D : TheoryTy ℓD tt}
  → A ⊢ C → B ⊢ D → A ⊗ B ⊢ C ⊗ D
⊗-map {ℓA = ℓA} {ℓB = ℓB} {ℓC = ℓC} {ℓD = ℓD} f g =
  ⊗map[ _⊙_ ][ two ℓA ℓB ] (two ℓC ℓD) λ where
    zero → f
    (suc zero) → g

_,⊗_ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
      {C : TheoryTy ℓC tt} {D : TheoryTy ℓD tt}
  → A ⊢ C → B ⊢ D → A ⊗ B ⊢ C ⊗ D
_,⊗_ = ⊗-map

infixr 20 _,⊗_

isSet⊗2 : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → isSetTheoryTy A → isSetTheoryTy B → isSetTheoryTy (A ⊗ B)
isSet⊗2 {A = A} {B = B} sA sB =
  isSet⊗ _⊙_ (two _ _) (A , B , tt*) λ where
    zero → sA
    (suc zero) → sB

⊗-assoc : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → (A ⊗ B) ⊗ C ⊢ A ⊗ (B ⊗ C)
⊗-assoc m (ms , e , ((ns , f , (a , (b , _))) , (c , _))) =
  two (ns zero) (ns (suc zero) ++ ms (suc zero))
    , split
    , (a , ((two (ns (suc zero)) (ms (suc zero)) , Eq.refl , (b , (c , tt*))) , tt*))
  where
  split : (ns zero ++ (ns (suc zero) ++ ms (suc zero))) Eq.≡ m
  split = Eq.sym (++-assocEq (ns zero) (ns (suc zero)) (ms (suc zero)))
     Eq.∙ (Eq.ap (_++ ms (suc zero)) f Eq.∙ e)

-- written out, not `⊗ᴰ-assoc⁻` at constant families: that typechecks but stops
-- reducing when passed unapplied — the families become metas nothing solves
⊗-assoc⁻ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → A ⊗ (B ⊗ C) ⊢ (A ⊗ B) ⊗ C
⊗-assoc⁻ m (ms , e , (a , ((ns , f , (b , (c , _))) , _))) =
  two (ms zero ++ ns zero) (ns (suc zero))
    , split
    , ((two (ms zero) (ns zero) , Eq.refl , (a , (b , tt*))) , (c , tt*))
  where
  split : ((ms zero ++ ns zero) ++ ns (suc zero)) Eq.≡ m
  split = ++-assocEq (ms zero) (ns zero) (ns (suc zero))
     Eq.∙ (Eq.ap (ms zero ++_) f Eq.∙ e)

⊗-unit-r⁻ : {A : TheoryTy ℓA tt} → A ⊢ A ⊗ ⊤Ty
⊗-unit-r⁻ m a = two m [] , Eq.pathToEq (++-unit-r m) , (a , (tt , tt*))

-- named so coherences can write the cast down instead of leaving it to unification
unit-lPath : {m : String} (ms : arities MonSig _⊙_ → String)
  → εTy (ms zero) → op _⊙_ ms Eq.≡ m → ms (suc zero) ≡ m
unit-lPath ms u e =
  cong (_++ ms (suc zero)) (Eq.eqToPath (u .snd .fst)) ∙ Eq.eqToPath e

⊗-unit-l : {A : TheoryTy ℓA tt} → εTy ⊗ A ⊢ A
⊗-unit-l {A = A} m (ms , e , (u , (a , _))) =
  Eq.transport A (Eq.pathToEq (unit-lPath ms u e)) a

⊗-unit-l⁻ : {A : TheoryTy ℓA tt} → A ⊢ ⊤Ty ⊗ A
⊗-unit-l⁻ m a = two [] m , Eq.refl , (tt , (a , tt*))

εTy-pt : εTy []
εTy-pt = (λ ()) , Eq.refl , tt*
