{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The theory's types, at a decidable alphabet.

   Fixing `_≟_` is what lets `Strings` be instantiated, and everything
   downstream -- the connectives, `μ`, covers, decidability, lookahead
   classes -- is that instantiation.  Nothing here is about parsing.

   It used to live at the top of `RecursiveDescent.List`, which meant a
   bottom-up parser had to import a recursive-descent module to get `⊗`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Types
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  where

open import Cubical.Data.Unit using (tt ; tt*)
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)

isSetAlphabet : isSet Alphabet
isSetAlphabet = Discrete→isSet λ x y → Sum.rec
  (λ p → yes (Eq.eqToPath p)) (λ ¬p → no λ p → ¬p (Eq.pathToEq p)) (x ≟ y)
  where open import Cubical.Relation.Nullary.Base using (yes ; no)

open import Theory.Instances.Monoid.Base public
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet public
open import Theory.Type.HLevels MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Inductive.HLevels MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Instances.Monoid.SemanticAction Alphabet isSetAlphabet public
  hiding (Δ)
open import Theory.Instances.Monoid.Lookahead.Base Alphabet isSetAlphabet public
open import Theory.Type.Cover.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Monad.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Monad.Maybe MonEqns Alphabet (λ _ → tt) listPresentation public
-- `at` clashes with the `_at_` of `SemanticAction`, which every test uses
open import Theory.Type.Decidable.Base MonEqns Alphabet (λ _ → tt) listPresentation public
  hiding (at)

private variable ℓA ℓB ℓC : Level

-- The connectives' h-levels and the distributivity `⊗⊕-distL` is missing
-- an inverse for.  `Strings` states the connectives but does not import
-- `HLevels`, so the set-ness of a binary `⊗` has to be said here.

isSet⊗2 : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → isSetTheoryTy A → isSetTheoryTy B → isSetTheoryTy (A ⊗ B)
isSet⊗2 {A = A} {B = B} sA sB =
  isSet⊗ _⊙_ (two _ _) (A , B , tt*) λ where
    zero → sA
    (suc zero) → sB
  where open import Cubical.Data.FinData using (zero ; suc)

isSetεTy : isSetTheoryTy εTy
isSetεTy = isSet⊗ ε· (λ ()) tt* λ ()

isSetLiteral : (c : Alphabet) → isSetTheoryTy (literal c)
isSetLiteral c _ = isProp→isSet isPropEqString

isSetDecTy : {A : TheoryTy ℓA tt} → isSetTheoryTy A → isSetTheoryTy (DecTy A)
isSetDecTy sA = isSet⊕ sA (isSet⇒ isSet⊥Ty)

⊗⊕-distL⁻ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → (A ⊗ C) ⊕ (B ⊗ C) ⊢ (A ⊕ B) ⊗ C
⊗⊕-distL⁻ = ⊕-elim (inl ,⊗ id⊢) (inr ,⊗ id⊢)

-- ...and it is an inverse: neither direction touches the splitting, so
-- both round trips are the `⊕`'s case split and nothing else.
⊗⊕-distL⁻∘distL : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → ⊗⊕-distL⁻ {A = A} {B = B} {C = C} ∘⊢ ⊗⊕-distL ≡ id⊢
⊗⊕-distL⁻∘distL = funExt λ m → funExt λ where
  (ms , e , (Sum.inl a , r)) → refl
  (ms , e , (Sum.inr b , r)) → refl

⊗⊕-distL∘distL⁻ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → ⊗⊕-distL {A = A} {B = B} {C = C} ∘⊢ ⊗⊕-distL⁻ ≡ id⊢
⊗⊕-distL∘distL⁻ = funExt λ m → funExt λ where
  (Sum.inl x) → refl
  (Sum.inr x) → refl

-- ...and the grammars that carry their set-ness, which is what a guarded
-- recursion asks of one.  `_&Set_` and `_⊕Set_` are in `HLevels`.

infixr 20 _⊗Set_

_⊗Set_ : TheorySet ℓA tt → TheorySet ℓB tt
  → TheorySet (ℓ-max ℓAlph (ℓ-max ℓA ℓB)) tt
(A , sA) ⊗Set (B , sB) = (A ⊗ B) , isSet⊗2 sA sB

DecSet : TheorySet ℓA tt → TheorySet ℓA tt
DecSet (A , sA) = DecTy A , isSetDecTy sA

litSet : (c : Alphabet) → TheorySet ℓM tt
litSet c = literal c , isSetLiteral c

charSet : TheorySet ℓM tt
charSet = char , isSet⊕ᴰ isSetAlphabet isSetLiteral

⊥Set : TheorySet ℓ-zero tt
⊥Set = ⊥Ty , isSet⊥Ty

εSet : TheorySet ℓM tt
εSet = εTy , isSetεTy

-- Deciding a lookahead class.  This is equality of classes, not a parser
-- combinator, so it sits with the classes.

_≟M_ : (o o' : M₁) → (o Eq.≡ o') Sum.⊎ ((o Eq.≡ o') → Empty.⊥)
ε₁ ≟M ε₁ = Sum.inl Eq.refl
ε₁ ≟M tk _ = Sum.inr λ ()
tk _ ≟M ε₁ = Sum.inr λ ()
tk c ≟M tk d with c ≟ d
... | Sum.inl Eq.refl = Sum.inl Eq.refl
... | Sum.inr ne = Sum.inr λ where Eq.refl → ne Eq.refl
