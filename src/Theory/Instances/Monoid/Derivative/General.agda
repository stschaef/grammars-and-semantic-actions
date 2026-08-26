{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The derivative of a grammar by a grammar, and its amazing right adjoint.

   `Theory/Type/Later/Derivative` already differentiates along a *function*
   of worlds: `Derivative f B = f* B` with `√ f = Π_f` right adjoint to it.
   That is the representable case.  Weighting by a whole grammar instead
   (sss-00PP, sss-00PR) gives

     (∂[ A ] B) w  ≅  Σ[ u ] (A u × B (u ++ w))
     (√[ A ] C) w  ≅  Π[ u v ] (u ++ v = w) → A u → C v

   fibrationally `Σ_π₂ (π₁*A × μ*B)` and `Π_μ (π₁*A ⇒ π₂*C)`, with
   `∂[ A ] ⊣ √[ A ]`.  Nothing below is fibrational; only the universal
   property is, and that is what is proved.

   Both formers are `opaque`.  Everything after the UMP block is therefore
   forced through `∂-intro`/`∂-intro⁻`, which is the point: facts about
   derivatives should be adjointness, not case analysis on splittings.
   The one place that unfolds is the bridge at the bottom, where the
   derivative is identified with Brzozowski's -- and, separately, with the
   residual.  Those are theorems about *this* model, not about `∂`.

   sss-00PS is the reason to keep them apart: `∂[ A ]` always has a right
   adjoint, the residual does not, and the two agree at `⌈ w ⌉ ` only
   because `u = w` is contractible there.  The Brzozowski derivative is a
   derivative first and a residual by accident. -}
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

------------------------------------------------------------------------
-- The two formers, and the adjunction between them.

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

  -- Contravariance in the weight is *not* a consequence of `∂[ A ] ⊣ √[ A ]`
  -- -- that adjunction relates nothing at two different weights -- so it is
  -- a second primitive of the interface, stated once and used opaquely
  -- after.  It is what lets a derivative by a longer word factor through a
  -- derivative by a shorter one.
  √-reweight : {A : TheoryTy ℓA tt} {A' : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
    → A ⊢ A' → √[ A' ] C ⊢ √[ A ] C
  √-reweight f m h u v p a = h u v p (f u a)

------------------------------------------------------------------------
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

  -- A left adjoint preserves colimits.  `Dl-⊕-out`/`Dl-⊕-in`/`Dl-map` in
  -- `Regex/Derivative` are these, done by hand over splittings.
  ∂-⊕ᴰ : {Y : Type ℓY} {B : Y → TheoryTy ℓB tt}
    → ∂[ A ] (⊕[ y ∈ Y ] B y) ⊢ ⊕[ y ∈ Y ] (∂[ A ] B y)
  ∂-⊕ᴰ = ∂-intro⁻ (⊕ᴰ-elim λ y → ∂-intro (σ⊕ y))

  ∂-⊕ᴰ⁻ : {Y : Type ℓY} {B : Y → TheoryTy ℓB tt}
    → ⊕[ y ∈ Y ] (∂[ A ] B y) ⊢ ∂[ A ] (⊕[ y ∈ Y ] B y)
  ∂-⊕ᴰ⁻ = ⊕ᴰ-elim λ y → ∂-map (σ⊕ y)

  ∂-⊥ : ∂[ A ] ⊥Ty ⊢ ⊥Ty
  ∂-⊥ = ∂-intro⁻ ⊥Ty-elim

-- reindexing the weight, from `√-reweight` above
∂-weight : {A : TheoryTy ℓA tt} {A' : TheoryTy ℓB tt} {B : TheoryTy ℓC tt}
  → A ⊢ A' → ∂[ A ] B ⊢ ∂[ A' ] B
∂-weight f = ∂-intro⁻ (√-reweight f ∘⊢ ∂-unit)

------------------------------------------------------------------------
-- The bridge: what `∂` is in this model.
--
-- `⌈ w ⌉ u` is `u Eq.≡ w`, a singleton, so the `Σ` and the `Π` over it
-- are both just the fibre at `w`.  That single fact is sss-00PS: it makes
-- the derivative agree with Brzozowski's *and* with the residual, and it
-- is the only reason the latter two have anything to do with each other.

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

  -- ...and the residual, which agrees only here
  ∂⌈⌉→⊸ : (w : String) {B : TheoryTy ℓB tt} → ∂[ ⌈ w ⌉ ] B ⊢ ⌈ w ⌉ ⊸ B
  ∂⌈⌉→⊸ w {B = B} m (u , p , b) l q = cast {X = B} (Eq.ap (_++ m) (p Eq.∙ Eq.sym q)) b

  ⊸→∂⌈⌉ : (w : String) {B : TheoryTy ℓB tt} → ⌈ w ⌉ ⊸ B ⊢ ∂[ ⌈ w ⌉ ] B
  ⊸→∂⌈⌉ w m h = w , Eq.refl , h w Eq.refl
