{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The associator and the two unitors are isomorphisms.

   These are `⊢`-term equations, not category theory: `Strings` and
   `Residual` introduce the maps by matching on splittings, and nothing there
   says the round trips are the identity.  Every client that reassociates a
   tensor and puts it back needs one of these. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.WildCat.LocallySmall.Base
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Unitor
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List as L using (List ; [] ; _∷_ ; _++_ ; ++-unit-r)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt ; tt* ; isPropUnit*)
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⊗ε-unit-l⁻ ; ⊗ε-unit-r ; ⊗ε-unit-r⁻ ; castEq ; castEqPathP ; two-η)

private variable ℓA ℓB ℓC ℓA' ℓB' ℓC' : Level

-- Two `castEq`s along inverse equations cancel, on the nose once the
-- equation is matched.
castEq-inv : {A : String → Type ℓA} {x y : String} (q : x Eq.≡ y) (a : A y)
  → castEq {A = A} q (castEq {A = A} (Eq.sym q) a) ≡ a
castEq-inv Eq.refl a = refl

-- `εTy`'s splitting is a function out of `Fin 0`, so it is a proposition --
-- but only up to `funExt`, since `Fin 0` has no η.
isPropεTy : (m : String) → isProp (εTy m)
isPropεTy m (ms , e , _) (ns , f , _) =
  ΣPathP ( funExt (λ ())
         , ΣPathP ( isProp→PathP (λ i → isPropEqString) e f
                  , isProp→PathP (λ i → isPropUnit*) tt* tt*))

module _ {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt} where

  -- Both reassociations keep the same three slots over the same word; they
  -- differ only in how the splitting is rebuilt, which is what `two≡` gives.
  ⊗-assoc⁻∘⊗-assoc : ⊗-assoc⁻ {A = A} {B = B} {C = C} ∘⊢ ⊗-assoc ≡ id⊢
  ⊗-assoc⁻∘⊗-assoc = funExt λ m → funExt (atPoint m)
    where
    atPoint : (m : String) (x : ((A ⊗ B) ⊗ C) m)
      → ⊗-assoc⁻ {A = A} {B = B} {C = C} m (⊗-assoc m x) ≡ x
    atPoint m (ms , e , ((ns , f , (a , (b , _))) , (c , _))) =
      ⊗PathP' {A = A ⊗ B} {B = C} refl
        (two≡ (Eq.eqToPath f) refl)
        (⊗PathP' {A = A} {B = B} (Eq.eqToPath f) (two≡ refl refl) refl refl)
        refl

  ⊗-assoc∘⊗-assoc⁻ : ⊗-assoc {A = A} {B = B} {C = C} ∘⊢ ⊗-assoc⁻ ≡ id⊢
  ⊗-assoc∘⊗-assoc⁻ = funExt λ m → funExt (atPoint m)
    where
    atPoint : (m : String) (x : (A ⊗ (B ⊗ C)) m)
      → ⊗-assoc {A = A} {B = B} {C = C} m (⊗-assoc⁻ m x) ≡ x
    atPoint m (ms , e , (a , ((ns , f , (b , (c , _))) , _))) =
      ⊗PathP' {A = A} {B = B ⊗ C} refl
        (two≡ refl (Eq.eqToPath f))
        refl
        (⊗PathP' {A = B} {B = C} (Eq.eqToPath f) (two≡ refl refl) refl refl)

module _ {A : TheoryTy ℓA tt} where

  -- The left unitor.  One direction is `unit-l≡` at a splitting whose left
  -- half is already `[]`; the other has to move the whole element along the
  -- splitting's own equation.
  ⊗-unit-l∘l⁻ : ⊗-unit-l {A = A} ∘⊢ ⊗ε-unit-l⁻ ≡ id⊢
  ⊗-unit-l∘l⁻ = funExt λ m → funExt λ a →
    sym (unit-l≡ {A = A} m (⊗ε-unit-l⁻ m a) refl)

  ⊗-unit-l⁻∘l : ⊗ε-unit-l⁻ ∘⊢ ⊗-unit-l {A = A} ≡ id⊢
  ⊗-unit-l⁻∘l = funExt λ m → funExt (atPoint m)
    where
    atPoint : (m : String) (t : (εTy ⊗ A) m)
      → ⊗ε-unit-l⁻ m (⊗-unit-l {A = A} m t) ≡ t
    atPoint m t@(ms , e , (u , (a , _))) =
      ⊗PathP' {A = εTy} {B = A} refl
        (two≡ (Eq.eqToPath (u .snd .fst)) (sym upath))
        (isProp→PathP (λ i → isPropεTy _) _ _)
        (symP (unit-l≡ {A = A} m t upath))
      where
      upath : ms (suc zero) ≡ m
      upath = unit-lPath ms u e

  -- The right unitor.  `⊗ε-unit-r` matches its argument's equation instead of
  -- transporting, so one composite is `castEq` bookkeeping; the other has to
  -- *match* the splitting's right half as `[]`, since nothing reduces until
  -- the `εTy` witness' equation is a constructor.  Writing the splitting as
  -- `two x y` is what makes the match legal; `two-η` puts an arbitrary
  -- splitting back into that form.
  ⊗-unit-r∘r⁻ : ⊗ε-unit-r {A = A} ∘⊢ ⊗ε-unit-r⁻ ≡ id⊢
  ⊗-unit-r∘r⁻ = funExt λ m → funExt λ a → castEq-inv {A = A} (++-unit-rEq m) a

  private
    unit-r-η : (m x : String) (us : arities MonSig ε· → String) (y : String)
      (e : op _⊙_ (two x y) Eq.≡ m) (a : A x) (q : op ε· us Eq.≡ y)
      → ⊗ε-unit-r⁻ m (⊗ε-unit-r {A = A} m
            (two x y , e , (a , ((us , q , tt*) , tt*))))
        ≡ (two x y , e , (a , ((us , q , tt*) , tt*)))
    unit-r-η m x us .(op ε· us) e a Eq.refl =
      ⊗PathP' {A = A} {B = εTy} refl (two≡ p refl)
        (compPathP' {B = A}
          (castEqPathP {A = A} e (sym (Eq.eqToPath e)) _)
          (castEqPathP {A = A} (Eq.sym (++-unit-rEq x)) (++-unit-r x) a))
        (isProp→PathP (λ i → isPropεTy _) _ _)
      where
      p : m ≡ x
      p = sym (Eq.eqToPath e) ∙ ++-unit-r x

  ⊗-unit-r⁻∘r : ⊗ε-unit-r⁻ ∘⊢ ⊗ε-unit-r {A = A} ≡ id⊢
  ⊗-unit-r⁻∘r = funExt λ m → funExt (atPoint m)
    where
    atPoint : (m : String) (t : (A ⊗ εTy) m)
      → ⊗ε-unit-r⁻ m (⊗ε-unit-r {A = A} m t) ≡ t
    atPoint m (ms , e , (a , ((us , q , _) , _))) =
      subst
        (λ ns → (r : op _⊙_ ns Eq.≡ m) (a' : A (ns zero))
                (q' : op ε· us Eq.≡ ns (suc zero))
              → ⊗ε-unit-r⁻ m (⊗ε-unit-r {A = A} m
                    (ns , r , (a' , ((us , q' , tt*) , tt*))))
                ≡ (ns , r , (a' , ((us , q' , tt*) , tt*))))
        (two-η ms)
        (unit-r-η m (ms zero) us (ms (suc zero)))
        e a q

-- Naturality, restated level-polymorphically: `Strings` states these only at
-- `ℓM`, though the proofs never mentioned the level.
module _ {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} where
  ⊗-unit-l-nat↑ : (f : A ⊢ B)
    → f ∘⊢ ⊗-unit-l {A = A} ≡ ⊗-unit-l {A = B} ∘⊢ ⊗-map (id⊢ {A = εTy}) f
  ⊗-unit-l-nat↑ f = funExt λ m → funExt λ where
    (ms , e , (u , (a , _))) →
      transportEq-nat f (Eq.pathToEq (unit-lPath ms u e)) a

-- The associator is natural in all three slots, on the nose: `⊗-map` never
-- touches the splitting and `⊗-assoc` never touches the slots.
module _ {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  {A' : TheoryTy ℓA' tt} {B' : TheoryTy ℓB' tt} {C' : TheoryTy ℓC' tt}
  (f : A ⊢ A') (g : B ⊢ B') (h : C ⊢ C') where

  ⊗-assoc-nat↑ : ⊗-assoc ∘⊢ ⊗-map (⊗-map f g) h
               ≡ ⊗-map f (⊗-map g h) ∘⊢ ⊗-assoc
  ⊗-assoc-nat↑ = refl

  ⊗-assoc⁻-nat↑ : ⊗-assoc⁻ ∘⊢ ⊗-map f (⊗-map g h)
                ≡ ⊗-map (⊗-map f g) h ∘⊢ ⊗-assoc⁻
  ⊗-assoc⁻-nat↑ = refl

-- The tensor is functorial on isomorphisms.  `⊗-map-∘` and `⊗-map-id` are
-- both `refl`, so only the two `cong`s remain.
module _ {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  {C : TheoryTy ℓC tt} {D : TheoryTy ℓA' tt}
  (A≅B : A ≅ B) (C≅D : C ≅ D) where
  open WildCatNotation
  open WildCatIso

  ⊗≅ : (A ⊗ C) ≅ (B ⊗ D)
  ⊗≅ .fun = ⊗-map (A≅B .fun) (C≅D .fun)
  ⊗≅ .inv = ⊗-map (A≅B .inv) (C≅D .inv)
  ⊗≅ .sec = cong₂ ⊗-map (A≅B .sec) (C≅D .sec)
  ⊗≅ .ret = cong₂ ⊗-map (A≅B .ret) (C≅D .ret)
