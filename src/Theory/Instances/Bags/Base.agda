{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- Bags: the theory of monoids extended by one permutation equation. -}
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

data CommEqn : Type ℓ-zero where
  comm : CommEqn

open import Theory.Instances.Monoid.Extension
  CommEqn (λ _ → 2)
  (λ _ → node _⊙_ var) (λ _ → node _⊙_ (λ b → var (swap b)))
  El public
  renaming ( Carrier to Bag
           ; _⊗ₑ_ to _⊎B_ ; ⊗ₑmap to ⊎Bmap ; ε⊗ to εB
           ; ⊗ₑ-assoc to ⊎B-assoc ; ⊗ₑ-assoc⁻ to ⊎B-assoc⁻
           ; ⊗ₑ-unitL to ⊎B-unitL ; ⊗ₑ-unitR to ⊎B-unitR
           ; ⊗ₑ-unitL⁻ to ⊎B-unitL⁻ ; ⊗ₑ-unitR⁻ to ⊎B-unitR⁻
           ; ⊗ₑ-unitL⌈⌉ to ⊎B-unitL⌈⌉
           ; _⊸ₑ_ to _⊸B_ ; ⊸ₑ-intro to ⊸B-intro ; ⊸ₑ-app to ⊸B-app
           ; ⊸ₑ-intro⁻ to ⊸B-intro⁻
           ; ε⊗→⌈ε⌉ to εB→⌈ε⌉ ; ⌈ε⌉→ε⊗ to ⌈ε⌉→εB
           ; ⊗ᵘ→⊗ₑ to ⊗ᵘ→⊎B ; ⊗ₑ→⊗ᵘ to ⊎B→⊗ᵘ
           ; K-⊗ₑ₁ to K-⊎B₁ ; K-⊗ₑ₂ to K-⊎B₂
           ; ⊗ₑ⊕ᴰ-dist to ⊎B⊕ᴰ-dist ; ⊗ₑ⊕-dist to ⊎B⊕-dist
           ; MonPlusEqns to BagEqns ; MonPlusEqn to BagEqn )

private variable ℓA ℓB : Level

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

opaque
  ⊙-inter : (a b c d : Bag) → (a ⊙ᵖ b) ⊙ᵖ (c ⊙ᵖ d) ≡ (a ⊙ᵖ c) ⊙ᵖ (b ⊙ᵖ d)
  ⊙-inter a b c d =
    ⊙-assoc a b (c ⊙ᵖ d)
    ∙ cong (a ⊙ᵖ_) (sym (⊙-assoc b c d) ∙ cong (_⊙ᵖ d) (⊙-comm b c)
                    ∙ ⊙-assoc c b d)
    ∙ sym (⊙-assoc a c (b ⊙ᵖ d))
