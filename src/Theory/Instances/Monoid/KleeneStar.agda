open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.KleeneStar
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Unit using (Unit ; tt)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet

private variable ℓA : Level

-- Right-nested lists of parses.  Keeping the branch as a named function is
-- important: it makes repeated occurrences of this code compare directly.
starBranch : TheoryTy ℓA tt → Bool → Functor ℓA Unit (λ _ → tt) tt
starBranch A false = ⊗e ε· λ ()
starBranch A true = ⊗e _⊙_ (two (k A) (Var tt))

StarCode : TheoryTy ℓA tt → Functor ℓA Unit (λ _ → tt) tt
StarCode A = ⊕e Bool (starBranch A)

Star : TheoryTy ℓA tt → TheoryTy (ℓF ℓA) tt
Star A = μ (λ _ → StarCode A) tt

_* : TheoryTy ℓA tt → TheoryTy (ℓF ℓA) tt
A * = Star A

infix 30 _*

NIL-branch : {ℓA : Level} {A : TheoryTy ℓA tt}
  → LiftTheoryTy (ℓF ℓA) εTy
  ⊢ ⟦ starBranch A false ⟧TheoryTy (λ _ → A *)
NIL-branch m p with p .lower
... | ms , e , u = ms , e , λ ()

NIL-code : {ℓA : Level} {A : TheoryTy ℓA tt}
  → ⟦ starBranch A false ⟧TheoryTy (λ _ → A *) ⊢ A *
NIL-code = roll ∘⊢ σ⊕ false

NIL : {ℓA : Level} {A : TheoryTy ℓA tt}
  → LiftTheoryTy (ℓF ℓA) εTy ⊢ A *
NIL = NIL-code ∘⊢ NIL-branch

CONS-branch : {ℓA : Level} {A : TheoryTy ℓA tt}
  → A ⊗ (A *) ⊢ ⟦ starBranch A true ⟧TheoryTy (λ _ → A *)
CONS-branch m (ms , e , a , as , u) =
  ms , e , two (lift a) (lift as)

CONS-code : {ℓA : Level} {A : TheoryTy ℓA tt}
  → ⟦ starBranch A true ⟧TheoryTy (λ _ → A *) ⊢ A *
CONS-code = roll ∘⊢ σ⊕ true

CONS : {ℓA : Level} {A : TheoryTy ℓA tt} → A ⊗ (A *) ⊢ A *
CONS = CONS-code ∘⊢ CONS-branch

fold*r : {ℓA ℓB : Level} {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → (⟦ starBranch A false ⟧TheoryTy (λ _ → B) ⊢ B)
  → (⟦ starBranch A true ⟧TheoryTy (λ _ → B) ⊢ B)
  → A * ⊢ B
fold*r {A = A} {B = B} nil cons = rec (λ _ → StarCode A) alg tt
  where
  alg : ∀ _ → ⟦ StarCode A ⟧TheoryTy (λ _ → B) ⊢ B
  alg _ = ⊕ᴰ-elim λ where
    false → nil
    true → cons
