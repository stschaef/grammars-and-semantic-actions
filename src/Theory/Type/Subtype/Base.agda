-- Subobjects, via the subobject classifier.  A subtype of `A` is a map
-- `A ⊢ Ω`, and `subTy p` is its pullback of `true`.
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence using (hPropExt)
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Subtype.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Empty as Empty

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Top.Base σeq V vs 𝒫
open import Theory.Type.HLevels σeq V vs 𝒫
open import Theory.Type.Inductive.Base σeq V vs 𝒫
open import Theory.Type.Equivalence.Base σeq V vs 𝒫
open import Theory.Type.Unambiguity.Base σeq V vs 𝒫

private variable ℓA ℓB ℓC ℓX ℓ' : Level

Ω : ∀ {ℓ'} {s} → TheoryTy (ℓ-suc ℓ') s
Ω {ℓ' = ℓ'} _ = hProp ℓ'

isSetΩ : ∀ {ℓ'} {s} → isSetTheoryTy (Ω {ℓ' = ℓ'} {s = s})
isSetΩ _ = isSetHProp

isSet⊢Ω : ∀ {s} {A : TheoryTy ℓA s} → isSet (A ⊢ Ω {ℓ' = ℓ'})
isSet⊢Ω = isSetΠ λ m → isSet→ isSetHProp

true : ∀ {s} → ⊤Ty {s = s} ⊢ Ω {ℓ' = ℓ'}
true _ _ .fst = Unit*
true _ _ .snd = isPropUnit*

false : ∀ {s} → ⊤Ty {s = s} ⊢ Ω {ℓ' = ℓ'}
false _ _ .fst = Empty.⊥*
false _ _ .snd = Empty.isProp⊥*

-- `p ≡ true ∘⊢ ⊤Ty-intro` is the internal way of saying "`p` holds of every
-- element of `A`"; every induction principle below produces one.
module SubTy {ℓ'} {s : S} {A : TheoryTy ℓA s} (p : A ⊢ Ω {ℓ' = ℓ'}) where
  subTy : TheoryTy (ℓ-max ℓA ℓ') s
  subTy m = Σ[ x ∈ A m ] ⟨ p m x ⟩

  sub-π : subTy ⊢ A
  sub-π _ = fst

  sub-π-pf : p ∘⊢ sub-π ≡ true ∘⊢ ⊤Ty-intro
  sub-π-pf = funExt λ m → funExt λ x →
    Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt (p m (x .fst) .snd) isPropUnit* (λ _ → tt*) λ _ → x .snd)

  module _ {B : TheoryTy ℓB s} (f : B ⊢ A)
    (pf : ∀ m x → ⟨ p m (f m x) ⟩) where
    insert-pf : p ∘⊢ f ≡ true ∘⊢ ⊤Ty-intro
    insert-pf = funExt λ m → funExt λ x →
      Σ≡Prop (λ _ → isPropIsProp)
        (hPropExt (p m (f m x) .snd) isPropUnit* (λ _ → tt*) λ _ → pf m x)

  module _ {B : TheoryTy ℓB s} (f : B ⊢ A)
    (pB : p ∘⊢ f ≡ true ∘⊢ ⊤Ty-intro) where
    extract-pf : ∀ m (x : B m) → ⟨ p m (f m x) ⟩
    extract-pf m x =
      transport (sym (cong fst (funExt⁻ (funExt⁻ pB m) x))) tt*

    sub-intro : B ⊢ subTy
    sub-intro m x .fst = f m x
    sub-intro m x .snd = extract-pf m x

    sub-β : sub-π ∘⊢ sub-intro ≡ f
    sub-β = refl

  module _ {B : TheoryTy ℓB s} (f : B ⊢ subTy) where
    private
      the-path : p ∘⊢ sub-π ∘⊢ f ≡ true ∘⊢ ⊤Ty-intro
      the-path = cong (_∘⊢ f) sub-π-pf

    -- η holds on the nose: `subTy` is a Σ and the second component is a
    -- proposition, so nothing has to be transported.
    sub-η : f ≡ sub-intro (sub-π ∘⊢ f) the-path
    sub-η i = f

  subTy-section : (f : A ⊢ subTy) → sub-π ∘⊢ f ≡ id⊢
    → p ≡ true ∘⊢ ⊤Ty-intro
  subTy-section f sec =
    cong (p ∘⊢_) (sym sec) ∙ cong (_∘⊢ f) sub-π-pf

  isMono-sub-π : isMono sub-π
  isMono-sub-π = injective→isMono λ m x y q →
    Σ≡Prop (λ z → p m z .snd) q

open SubTy public

-- Induction: to prove `p` of every element of an inductive type it is enough
-- to prove it of one layer whose subterms already satisfy it.
module _ {ℓ'} {X : Type ℓX} {xs : X → S}
  (F : (x : X) → Functor ℓA X xs (xs x))
  (p : ∀ (x : X) → μ F x ⊢ Ω {ℓ' = ℓ'})
  (pf : ∀ (x : X) →
    p x ∘⊢ roll ∘⊢ map (F x) (λ y → sub-π (p y)) ≡ true ∘⊢ ⊤Ty-intro)
  where

  subTy-ind-alg : ∀ x
    → ⟦ F x ⟧TheoryTy (λ y → subTy (p y)) ⊢ subTy (p x)
  subTy-ind-alg x =
    sub-intro (p x) (roll ∘⊢ map (F x) (λ y → sub-π (p y))) (pf x)

  subTy-ind' : ∀ (x : X) → μ F x ⊢ subTy (p x)
  subTy-ind' = rec F subTy-ind-alg

  -- `sub-π` is an algebra map by `sub-β`, so `rec-section` -- which is the
  -- initiality argument, already packaged -- does the whole induction.
  sub-π-section : ∀ x → sub-π (p x) ∘⊢ subTy-ind' x ≡ id⊢
  sub-π-section = rec-section F subTy-ind-alg (λ y → sub-π (p y)) λ y → refl

  subTy-ind : ∀ (x : X) → p x ≡ true ∘⊢ ⊤Ty-intro
  subTy-ind x =
    subTy-section (p x) (subTy-ind' x) (sub-π-section x)

module _ {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  (f : B ⊢ A) (p : A ⊢ Ω {ℓ' = ℓ'}) where

  preimage : TheoryTy (ℓ-max ℓB ℓ') s
  preimage = subTy (p ∘⊢ f)

  preimage-map : preimage ⊢ subTy p
  preimage-map = sub-intro p (f ∘⊢ sub-π (p ∘⊢ f)) (sub-π-pf (p ∘⊢ f))

-- Every mono into a set is a subobject.
module _ {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  (f : B ⊢ A) (isSetA : isSetTheoryTy A) (isMono-f : isMono f) where

  mono-prop : A ⊢ Ω {ℓ' = ℓ-max ℓA ℓB}
  mono-prop m x .fst = Σ[ y ∈ B m ] f m y ≡ x
  mono-prop m x .snd = isMono→hasPropFibers isSetA isMono-f m x

  mono→subTy : TheoryTy (ℓ-max ℓA ℓB) s
  mono→subTy = subTy mono-prop

module _ {s : S} {A : TheoryTy ℓA s} (unambig-A : unambiguous A)
  (B : TheoryTy ℓB s) where

  unambiguous-prop : B ⊢ Ω {ℓ' = ℓA}
  unambiguous-prop m _ .fst = A m
  unambiguous-prop m _ .snd = unambig-A m

  unambiguous→subTy : TheoryTy (ℓ-max ℓB ℓA) s
  unambiguous→subTy = subTy unambiguous-prop
