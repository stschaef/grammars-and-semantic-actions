{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Nullability, and the split of any grammar by whether its word is empty.

   `¬Nullable` itself is `KleeneStar.Guarded`'s -- it is `disjoint A εTy`,
   the binary case of `Type.Unambiguity.Disjoint`.  What is added here is the
   *split*: every grammar is its empty part plus its nonempty part, and the
   case analysis is `stringLayer↑`, never an inspection of a splitting.

   NOTE: `Automaton.Greedy` independently states `¬Nullable-map`,
   `⊕ᴰ-¬Nullable`, `char⁺-¬Nullable` and `¬Nullable→char⁺`.  They are
   restated here so that this layer depends only on grammars, not on
   automata; that file could import them from here instead. -}
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
  using (&⊕-distR ; &⊕ᴰ-distL)
open import Theory.Type.Decidable.Base MonEqns Alphabet (λ _ → tt)
  listPresentation using (¬Ty) public
open import Theory.Instances.Monoid.Greedy.Base Alphabet isSetAlphabet
  using (char⁺) public

private variable ℓA ℓB ℓY : Level

-- `¬Nullable` transfers backwards along any map.
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

-- The split.  `stringLayer↑` is the case analysis; `&⊕-distR` moves it
-- under the `&`.  This is the internal form of the old `&string-split≅`.
stringSplit : {A : TheoryTy ℓA tt} → A ⊢ (A & εTy) ⊕ (A & char⁺)
stringSplit = &⊕-distR ∘⊢ (id⊢ ,& (stringLayer↑ ∘⊢ read ∘⊢ ⊤Ty-intro))

stringSplit⁻ : {A : TheoryTy ℓA tt} → (A & εTy) ⊕ (A & char⁺) ⊢ A
stringSplit⁻ = ⊕-elim π₁ π₁

-- ...so a non-nullable grammar is entirely its nonempty part, and anything
-- landing in `char⁺` is non-nullable.
¬Nullable→char⁺ : {A : TheoryTy ℓA tt} → ¬Nullable A → A ⊢ char⁺
¬Nullable→char⁺ nu = ⊕-elim (⊥Ty-elim ∘⊢ nu) π₂ ∘⊢ stringSplit

char⁺→¬Nullable : {A : TheoryTy ℓA tt} → A ⊢ char⁺ → ¬Nullable A
char⁺→¬Nullable f = ¬Nullable-map f char⁺-¬Nullable

¬Nullable-&char⁺ : {A : TheoryTy ℓA tt} → ¬Nullable (A & char⁺)
¬Nullable-&char⁺ = &-¬NullableR char⁺-¬Nullable

-- a non-nullable grammar is refuted at ε
¬Nullable→¬ε : {A : TheoryTy ℓA tt} → ¬Nullable A → εTy ⊢ ¬Ty A
¬Nullable→¬ε nu = ⇒-intro (nu ∘⊢ &-swap)

-- the two ways a tensor inherits non-nullability
¬Nullable⊗l : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → ¬Nullable A → ¬Nullable (A ⊗ B)
¬Nullable⊗l = ⊗-¬Nullable

¬Nullable⊗r : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → ¬Nullable B → ¬Nullable (A ⊗ B)
¬Nullable⊗r = ⊗-¬NullableR
