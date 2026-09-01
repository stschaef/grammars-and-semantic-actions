{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Laws of `⟦⊗e⟧`: the ⊗e-summand/binary-tensor passage is an isomorphism
   and `map` crosses it.  The last definitions that bind a model element. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Convolution
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⟦⊗e⟧ ; ⟦⊗e⟧⁻ ; two-η) public

private variable ℓA ℓB ℓC ℓX : Level

module _ {X : Type ℓX} {xs : X → Unit} (Fa Fb : Functor ℓA X xs tt) where

  module _ {A : (x : X) → TheoryTy ℓB tt} where

    -- `Fin 2` has no η, so this is `two-η` and nothing else
    ⟦⊗e⟧-η : ⟦⊗e⟧⁻ {A = A} Fa Fb ∘⊢ ⟦⊗e⟧ {A = A} Fa Fb ≡ id⊢
    ⟦⊗e⟧-η = funExt λ m → funExt λ where
      x@(ms , e , slots) i →
        ms , e
        , funExt {f = ⟦⊗e⟧⁻ Fa Fb m (⟦⊗e⟧ Fa Fb m x) .snd .snd} {g = slots}
            (λ where
              zero → refl
              (suc zero) → refl) i

    ⟦⊗e⟧-β : ⟦⊗e⟧ {A = A} Fa Fb ∘⊢ ⟦⊗e⟧⁻ {A = A} Fa Fb ≡ id⊢
    ⟦⊗e⟧-β = refl

  -- `map` at an `⊗e` summand *is* the tensor.s functorial action, so
  -- homomorphism proofs stay inside the DSL and never look at the splitting
  ⟦⊗e⟧-nat : {A : (x : X) → TheoryTy ℓB tt} {B : (x : X) → TheoryTy ℓC tt}
    (f : ∀ x → A x ⊢ B x)
    → ⟦⊗e⟧ {A = B} Fa Fb ∘⊢ map (⊗e _⊙_ (two Fa Fb)) f
      ≡ ⊗-map (map Fa f) (map Fb f) ∘⊢ ⟦⊗e⟧ {A = A} Fa Fb
  ⟦⊗e⟧-nat f = refl

  ⟦⊗e⟧⁻-nat : {A : (x : X) → TheoryTy ℓB tt} {B : (x : X) → TheoryTy ℓC tt}
    (f : ∀ x → A x ⊢ B x)
    → map (⊗e _⊙_ (two Fa Fb)) f ∘⊢ ⟦⊗e⟧⁻ {A = A} Fa Fb
      ≡ ⟦⊗e⟧⁻ {A = B} Fa Fb ∘⊢ ⊗-map (map Fa f) (map Fb f)
  ⟦⊗e⟧⁻-nat f = funExt λ m → funExt λ where
    x@(ms , e , _) i →
      ms , e
      , funExt
          {f = map (⊗e _⊙_ (two Fa Fb)) f m (⟦⊗e⟧⁻ Fa Fb m x) .snd .snd}
          {g = ⟦⊗e⟧⁻ Fa Fb m (⊗-map (map Fa f) (map Fb f) m x) .snd .snd}
          (λ where
            zero → refl
            (suc zero) → refl) i

module _ {X : Type ℓX} {xs : X → Unit} where

  -- nullary convolution is `εTy`: the slots are a function out of `Fin 0`
  ⊗e-ε→ : {A : (x : X) → TheoryTy ℓB tt} (F : interpIn ε· (Functor ℓA X xs))
    → ⟦ ⊗e ε· F ⟧TheoryTy A ⊢ εTy
  ⊗e-ε→ F m (ms , e , _) = ms , e , tt*

  ⊗e-ε← : {A : (x : X) → TheoryTy ℓB tt} (F : interpIn ε· (Functor ℓA X xs))
    → εTy ⊢ ⟦ ⊗e ε· F ⟧TheoryTy A
  ⊗e-ε← F m (ms , e , _) = ms , e , λ ()

  ⊗e-ε-map : {A : (x : X) → TheoryTy ℓB tt} {B : (x : X) → TheoryTy ℓC tt}
    (F : interpIn ε· (Functor ℓA X xs)) (f : ∀ x → A x ⊢ B x)
    → map (⊗e ε· F) f ≡ ⊗e-ε← {A = B} F ∘⊢ ⊗e-ε→ {A = A} F
  ⊗e-ε-map F f = funExt λ m → funExt λ where
    x@(ms , e , _) i →
      ms , e
      , funExt {f = map (⊗e ε· F) f m x .snd .snd}
          {g = ⊗e-ε← F m (⊗e-ε→ F m x) .snd .snd} (λ ()) i
