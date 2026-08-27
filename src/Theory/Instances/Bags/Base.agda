{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- Bags: the theory of monoids extended by one permutation equation.

   Everything that follows from the monoid equations alone -- `⊗ₑ` and its
   map, associator and unitors, the residual `⊸ₑ`, and the carrier-level
   `⊙-assoc`/`⊙-unitL`/`⊙-unitR` -- is inherited from
   `Monoid/Extension`, which takes `MonEqns`' three equations literally.
   What is here is the commutativity: the equation, its transport
   `⊎B-comm`, and `⊙-inter`, which is the only consequence that mixes it
   with associativity. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Equality as Eq
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)
open SortedSig
open SortedEqns
open import Theory.Instances.Monoid.Base
module Theory.Instances.Bags.Base (El : Type ℓ-zero) where

open import Cubical.Data.Sigma

-- The one extra equation: `x ⊙ y = y ⊙ x`, as a permutation of the slots.
data CommEqn : Type ℓ-zero where
  comm : CommEqn

open import Theory.Instances.Monoid.Extension
  CommEqn (λ _ → 2)
  (λ _ → node _⊙_ var) (λ _ → node _⊙_ (λ b → var (swap b)))
  El public

private variable ℓA ℓB : Level

Bag : Type ℓM
Bag = Carrier

infixr 20 _⊎B_
_⊎B_ : TheoryTy ℓA tt → TheoryTy ℓB tt → TheoryTy _ tt
_⊎B_ = _⊗ₑ_

private
  fromTm : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
    → ⟪ node _⊙_ (λ b → var (swap b)) ⟫[ two ℓA ℓB ] (A , B , tt*) ⊢ B ⊎B A
  fromTm m (ρ , e , (x , y , tt*)) = (λ b → ρ (swap b)) , e , (y , x , tt*)

⊎B-comm : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} → A ⊎B B ⊢ B ⊎B A
⊎B-comm {ℓA = ℓA} {ℓB = ℓB} {A = A} {B = B} =
  fromTm {A = A} {B = B} ∘⊢ eqn→fun (ext comm) (two ℓA ℓB) (A , B , tt*)

opaque
  ⊙-comm : (a b : Bag) → a ⊙ᵖ b ≡ b ⊙ᵖ a
  ⊙-comm a b =
    M .snd .snd (ext comm) (two a b)
    ∙ cong (op _⊙_) (funExt (two refl refl))

-- the interchange law: the one place commutativity meets associativity
opaque
  ⊙-inter : (a b c d : Bag) → (a ⊙ᵖ b) ⊙ᵖ (c ⊙ᵖ d) ≡ (a ⊙ᵖ c) ⊙ᵖ (b ⊙ᵖ d)
  ⊙-inter a b c d =
    ⊙-assoc a b (c ⊙ᵖ d)
    ∙ cong (a ⊙ᵖ_) (sym (⊙-assoc b c d) ∙ cong (_⊙ᵖ d) (⊙-comm b c)
                    ∙ ⊙-assoc c b d)
    ∙ sym (⊙-assoc a c (b ⊙ᵖ d))
