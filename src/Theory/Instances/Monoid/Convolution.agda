{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The laws of `⟦⊗e⟧`.

   `Residual` introduces the passage between a code's `⊗e` summand and the
   binary tensor; it does not say that the passage is an isomorphism, nor how
   `map` crosses it.  Both are stated here, at the same tier -- these are the
   last definitions that bind a model element.  Everything downstream builds
   an automaton, a parser or a construction *in the DSL*, and reaches an
   `⊗e` summand only through the three equations below. -}
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

    -- Splitting the convolution and putting it back is the identity: `Fin 2`
    -- has no η, so this is `two-η` and nothing else.
    ⟦⊗e⟧-η : ⟦⊗e⟧⁻ {A = A} Fa Fb ∘⊢ ⟦⊗e⟧ {A = A} Fa Fb ≡ id⊢
    ⟦⊗e⟧-η = funExt λ m → funExt λ where
      x@(ms , e , slots) i →
        ms , e
        , funExt {f = ⟦⊗e⟧⁻ Fa Fb m (⟦⊗e⟧ Fa Fb m x) .snd .snd} {g = slots}
            (λ where
              zero → refl
              (suc zero) → refl) i

    -- The other way round there is nothing to prove: the pair was built
    -- slotwise to begin with.
    ⟦⊗e⟧-β : ⟦⊗e⟧ {A = A} Fa Fb ∘⊢ ⟦⊗e⟧⁻ {A = A} Fa Fb ≡ id⊢
    ⟦⊗e⟧-β = refl

  -- `map` at an `⊗e` summand *is* the tensor's functorial action.  This is
  -- what lets a homomorphism proof over a labelled transition stay inside
  -- the DSL: it never has to look at the splitting.
  ⟦⊗e⟧-nat : {A : (x : X) → TheoryTy ℓB tt} {B : (x : X) → TheoryTy ℓC tt}
    (f : ∀ x → A x ⊢ B x)
    → ⟦⊗e⟧ {A = B} Fa Fb ∘⊢ map (⊗e _⊙_ (two Fa Fb)) f
      ≡ ⊗-map (map Fa f) (map Fb f) ∘⊢ ⟦⊗e⟧ {A = A} Fa Fb
  ⟦⊗e⟧-nat f = refl

  -- The same fact read backwards, which is the direction a constructor is
  -- built in.
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

  -- The nullary convolution is `εTy` whatever slot family it carries: the
  -- slots are a function out of `Fin 0`.
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
