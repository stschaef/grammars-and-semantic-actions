-- The equalizer is the subobject classified by "the two maps agree" — what buys `eq-η`.
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Subobject.Equalizer
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Sigma

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Top.Base σeq V vs 𝒫
open import Theory.Type.HLevels.Base σeq V vs 𝒫
open import Theory.Type.Equalizer.Base σeq V vs 𝒫
open import Theory.Type.Equivalence.Base σeq V vs 𝒫
open import Theory.Type.Subobject.Base σeq V vs 𝒫

private variable ℓA ℓB ℓC : Level

module _ {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  (isSetB : isSetTheoryTy B) (f f' : A ⊢ B) where

  eq-prop : A ⊢ Ω {ℓ' = ℓB}
  eq-prop m x .fst = f m x ≡ f' m x
  eq-prop m x .snd = isSetB m (f m x) (f' m x)

  -- not merely an iso: `subobject eq-prop` is `equalizer f f'` on the nose
  equalizer≡subobject : equalizer f f' ≡ subobject eq-prop
  equalizer≡subobject = refl

  eq-π-pf' : eq-prop ∘⊢ eq-π f f' ≡ true ∘⊢ ⊤Ty-intro
  eq-π-pf' = sub-π-pf eq-prop

  isMono-eq-π : isMono (eq-π f f')
  isMono-eq-π = isMono-sub-π eq-prop

  -- the witness is a proposition, so maps agreeing after `eq-π` agree
  module _ {C : TheoryTy ℓC s} (h : C ⊢ equalizer f f')
    (p : f ∘⊢ (eq-π f f' ∘⊢ h) ≡ f' ∘⊢ (eq-π f f' ∘⊢ h)) where
    eq-η : h ≡ eq-intro f f' (eq-π f f' ∘⊢ h) p
    eq-η = funExt λ m → funExt λ x →
      Σ≡Prop (λ y → isSetB m (f m y) (f' m y)) refl

  eq-ext : {C : TheoryTy ℓC s} (h h' : C ⊢ equalizer f f')
    → eq-π f f' ∘⊢ h ≡ eq-π f f' ∘⊢ h' → h ≡ h'
  eq-ext = isMono-eq-π
