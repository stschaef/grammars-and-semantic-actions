-- TODO how much of this Monad/ dir is actually used?
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Monad.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Theory.Base σeq V vs 𝒫

-- TODO use an upstream interface for defining Monads
-- perhaps on a locally small cat?
record Monad : Typeω where
  field
    ℓT : Level → Level
    T : ∀ {ℓA} {s} → TheoryTy ℓA s → TheoryTy (ℓT ℓA) s
    η : ∀ {ℓA} {s} {A : TheoryTy ℓA s} → A ⊢ T A
    bind : ∀ {ℓA ℓB} {s} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
      → A ⊢ T B → T A ⊢ T B

    bind-η : ∀ {ℓA} {s} {A : TheoryTy ℓA s} → bind (η {A = A}) ≡ id⊢
    bind-β : ∀ {ℓA ℓB} {s} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
      (f : A ⊢ T B) → bind f ∘⊢ η ≡ f
    bind-assoc : ∀ {ℓA ℓB ℓC} {s}
      {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {C : TheoryTy ℓC s}
      (g : B ⊢ T C) (f : A ⊢ T B)
      → bind g ∘⊢ bind f ≡ bind (bind g ∘⊢ f)

  fmap : ∀ {ℓA ℓB} {s} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
    → A ⊢ B → T A ⊢ T B
  fmap f = bind (η ∘⊢ f)

  join : ∀ {ℓA} {s} {A : TheoryTy ℓA s} → T (T A) ⊢ T A
  join = bind id⊢

open Monad public
