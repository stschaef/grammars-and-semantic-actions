{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The split of a grammar by whether its word is empty; the case analysis
   is `stringLayer↑`, never inspection of a splitting.
   NOTE: `Automaton.Greedy` independently states `¬Nullable-map`,
   `⊕ᴰ-¬Nullable`, `char⁺-¬Nullable`, `¬Nullable→char⁺`; it could import
   them from here instead. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.SequentialUnambiguity.Nullable
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Unit using (Unit ; tt)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar.Guarded Alphabet isSetAlphabet
  public
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (&⊕-distR)
open import Theory.Type.Decidable.Base MonEqns Alphabet (λ _ → tt)
  listPresentation using (¬Ty) public
open import Theory.Instances.Monoid.Greedy.Base Alphabet isSetAlphabet
  using (char⁺) public

private variable ℓA ℓB ℓY : Level

¬Nullable-map : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → A ⊢ B → ¬Nullable B → ¬Nullable A
¬Nullable-map f nu = nu ∘⊢ (f ,&p id⊢)

&-¬NullableL : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → ¬Nullable A → ¬Nullable (A & B)
&-¬NullableL = ¬Nullable-map π₁

&-¬NullableR : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → ¬Nullable B → ¬Nullable (A & B)
&-¬NullableR = ¬Nullable-map π₂

⊕ᴰ-¬Nullable : {Y : Type ℓY} {A : Y → TheoryTy ℓA tt}
  → ((y : Y) → ¬Nullable (A y)) → ¬Nullable (⊕[ y ∈ Y ] A y)
⊕ᴰ-¬Nullable nu = ⊕ᴰ-elim nu ∘⊢ &⊕ᴰ-distL

char⁺-¬Nullable : ¬Nullable char⁺
char⁺-¬Nullable = ⊗-¬Nullable char-¬Nullable

stringSplit : {A : TheoryTy ℓA tt} → A ⊢ (A & εTy) ⊕ (A & char⁺)
stringSplit = &⊕-distR ∘⊢ (id⊢ ,& (stringLayer↑ ∘⊢ read ∘⊢ ⊤Ty-intro))

stringSplit⁻ : {A : TheoryTy ℓA tt} → (A & εTy) ⊕ (A & char⁺) ⊢ A
stringSplit⁻ = ⊕-elim π₁ π₁

¬Nullable→char⁺ : {A : TheoryTy ℓA tt} → ¬Nullable A → A ⊢ char⁺
¬Nullable→char⁺ nu = ⊕-elim (⊥Ty-elim ∘⊢ nu) π₂ ∘⊢ stringSplit

char⁺→¬Nullable : {A : TheoryTy ℓA tt} → A ⊢ char⁺ → ¬Nullable A
char⁺→¬Nullable f = ¬Nullable-map f char⁺-¬Nullable

¬Nullable-&char⁺ : {A : TheoryTy ℓA tt} → ¬Nullable (A & char⁺)
¬Nullable-&char⁺ = &-¬NullableR char⁺-¬Nullable

¬Nullable→¬ε : {A : TheoryTy ℓA tt} → ¬Nullable A → εTy ⊢ ¬Ty A
¬Nullable→¬ε nu = ⇒-intro (nu ∘⊢ &-swap)

