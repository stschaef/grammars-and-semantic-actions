{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Derivative of a grammar by a grammar, and its right adjoint:

     (∂[ A ] B) w  ≅  Σ[ u ] (A u × B (u ++ w))
     (√[ A ] C) w  ≅  Π[ u v ] (u ++ v = w) → A u → C v

   `∂[ A ] ⊣ √[ A ]` (sss-00PP, sss-00PR); both formers are `opaque`.
   The residual agrees only at `⌈ w ⌉`, where `u = w` is contractible
   (sss-00PS). -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Derivative.General
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.List using ([] ; _∷_ ; _++_)
open import Cubical.Data.Sigma using (Σ ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet using (_⊸_)
open import Theory.Instances.Monoid.Derivative Alphabet isSetAlphabet
  using (Dl-string)

private
  variable
    ℓA ℓB ℓB' ℓC ℓY : Level

  -- matching the equation, so the cast vanishes on canonical input
  cast : {X : String → Type ℓA} {x y : String} → x Eq.≡ y → X x → X y
  cast Eq.refl b = b

opaque
  -- sss-00PP
  ∂[_]_ : TheoryTy ℓA tt → TheoryTy ℓB tt → TheoryTy (ℓ-max ℓM (ℓ-max ℓA ℓB)) tt
  (∂[ A ] B) w = Σ[ u ∈ String ] (A u × B (u ++ w))

  -- sss-00PR
  √[_]_ : TheoryTy ℓA tt → TheoryTy ℓC tt → TheoryTy (ℓ-max ℓM (ℓ-max ℓA ℓC)) tt
  (√[ A ] C) w = (u v : String) → (u ++ v) Eq.≡ w → A u → C v

opaque
  unfolding ∂[_]_ √[_]_

  ∂-intro : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
    → ∂[ A ] B ⊢ C → B ⊢ √[ A ] C
  ∂-intro e m b u v p a = e v (u , a , cast (Eq.sym p) b)

  ∂-intro⁻ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
    → B ⊢ √[ A ] C → ∂[ A ] B ⊢ C
  ∂-intro⁻ e w (u , a , b) = e (u ++ w) b u w Eq.refl a

  ∂-β : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
    (e : ∂[ A ] B ⊢ C) → ∂-intro⁻ {A = A} (∂-intro e) ≡ e
  ∂-β e = refl

  ∂-η : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
    (e : B ⊢ √[ A ] C) → ∂-intro {A = A} (∂-intro⁻ e) ≡ e
  ∂-η e = funExt λ m → funExt λ b → funExt λ u → funExt λ v →
    funExt λ where Eq.refl → refl

  ∂Iso : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
    → Iso (∂[ A ] B ⊢ C) (B ⊢ √[ A ] C)
  ∂Iso .Iso.fun = ∂-intro
  ∂Iso .Iso.inv = ∂-intro⁻
  ∂Iso .Iso.sec = ∂-η
  ∂Iso .Iso.ret = ∂-β

  -- contravariance in the weight is NOT a consequence of the adjunction
  -- (which relates nothing at two weights): a second primitive, letting a
  -- longer-word derivative factor through a shorter one
  √-reweight : {A : TheoryTy ℓA tt} {A' : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
    → A ⊢ A' → √[ A' ] C ⊢ √[ A ] C
  √-reweight f m h u v p a = h u v p (f u a)

-- Everything below uses only the adjunction.

module _ {A : TheoryTy ℓA tt} where
  ∂-unit : {B : TheoryTy ℓB tt} → B ⊢ √[ A ] (∂[ A ] B)
  ∂-unit = ∂-intro id⊢

  ∂-counit : {C : TheoryTy ℓC tt} → ∂[ A ] (√[ A ] C) ⊢ C
  ∂-counit = ∂-intro⁻ id⊢

  ∂-map : {B : TheoryTy ℓB tt} {B' : TheoryTy ℓB' tt}
    → B ⊢ B' → ∂[ A ] B ⊢ ∂[ A ] B'
  ∂-map f = ∂-intro⁻ (∂-unit ∘⊢ f)

  √-map : {C : TheoryTy ℓC tt} {C' : TheoryTy ℓB tt}
    → C ⊢ C' → √[ A ] C ⊢ √[ A ] C'
  √-map g = ∂-intro (g ∘⊢ ∂-counit)

  -- left adjoints preserve colimits; `Regex/Derivative` does these by hand
  ∂-⊕ᴰ : {Y : Type ℓY} {B : Y → TheoryTy ℓB tt}
    → ∂[ A ] (⊕[ y ∈ Y ] B y) ⊢ ⊕[ y ∈ Y ] (∂[ A ] B y)
  ∂-⊕ᴰ = ∂-intro⁻ (⊕ᴰ-elim λ y → ∂-intro (σ⊕ y))

  ∂-⊕ᴰ⁻ : {Y : Type ℓY} {B : Y → TheoryTy ℓB tt}
    → ⊕[ y ∈ Y ] (∂[ A ] B y) ⊢ ∂[ A ] (⊕[ y ∈ Y ] B y)
  ∂-⊕ᴰ⁻ = ⊕ᴰ-elim λ y → ∂-map (σ⊕ y)

  ∂-⊥ : ∂[ A ] ⊥Ty ⊢ ⊥Ty
  ∂-⊥ = ∂-intro⁻ ⊥Ty-elim
-- bridge (sss-00PS): `⌈ w ⌉ u` is `u Eq.≡ w`, a singleton, so `Σ` and `Π`
-- over it are the fibre at `w` -- whence agreement with both Brzozowski's
-- derivative and the residual

opaque
  unfolding ∂[_]_ √[_]_

  ∂⌈⌉→Dl : (w : String) {B : TheoryTy ℓB tt} → ∂[ ⌈ w ⌉ ] B ⊢ Dl-string w B
  ∂⌈⌉→Dl w {B = B} m (u , p , b) = cast {X = B} (Eq.ap (_++ m) p) b

  Dl→∂⌈⌉ : (w : String) {B : TheoryTy ℓB tt} → Dl-string w B ⊢ ∂[ ⌈ w ⌉ ] B
  Dl→∂⌈⌉ w m b = w , Eq.refl , b

  ∂⌈⌉-Dl-ret : (w : String) {B : TheoryTy ℓB tt}
    → ∂⌈⌉→Dl w {B = B} ∘⊢ Dl→∂⌈⌉ w ≡ id⊢
  ∂⌈⌉-Dl-ret w = refl

  ∂⌈⌉-Dl-sec : (w : String) {B : TheoryTy ℓB tt}
    → Dl→∂⌈⌉ w {B = B} ∘⊢ ∂⌈⌉→Dl w ≡ id⊢
  ∂⌈⌉-Dl-sec w = funExt λ m → funExt λ where (u , Eq.refl , b) → refl

  -- the residual agrees only here
  ∂⌈⌉→⊸ : (w : String) {B : TheoryTy ℓB tt} → ∂[ ⌈ w ⌉ ] B ⊢ ⌈ w ⌉ ⊸ B
  ∂⌈⌉→⊸ w {B = B} m (u , p , b) l q = cast {X = B} (Eq.ap (_++ m) (p Eq.∙ Eq.sym q)) b

  ⊸→∂⌈⌉ : (w : String) {B : TheoryTy ℓB tt} → ⌈ w ⌉ ⊸ B ⊢ ∂[ ⌈ w ⌉ ] B
  ⊸→∂⌈⌉ w m h = w , Eq.refl , h w Eq.refl
