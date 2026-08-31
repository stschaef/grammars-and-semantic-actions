{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Derivative
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.List using (_∷_ ; _++_)
open import Cubical.Data.Unit using (tt)
open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet

private variable ℓA ℓB : Level

-- The two one-hole contexts for multiplication.  They are the generic
-- `HoleVals` presentation of fixing the right or left string respectively.
rightCtx : String → HoleVals 2 (λ _ → tt) zero
rightCtx w zero = w

leftCtx : String → HoleVals 2 (λ _ → tt) (suc zero)
leftCtx w = w , λ ()

-- String-indexed Brzozowski derivatives, now obtained by specializing the
-- generic operation derivative to monoid multiplication.
Dr-string : String → TheoryTy ℓA tt → TheoryTy ℓA tt
Dr-string w = DerivativeAt _⊙_ zero (rightCtx w)

Dl-string : String → TheoryTy ℓA tt → TheoryTy ℓA tt
Dl-string w = DerivativeAt _⊙_ (suc zero) (leftCtx w)

√r-string : String → TheoryTy ℓA tt → TheoryTy _ tt
√r-string w = √At _⊙_ zero (rightCtx w)

√l-string : String → TheoryTy ℓA tt → TheoryTy _ tt
√l-string w = √At _⊙_ (suc zero) (leftCtx w)

√r-string-Iso : (w : String) {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → Iso (Dr-string w B ⊢ A) (B ⊢ √r-string w A)
√r-string-Iso w = √AtIso _⊙_ zero (rightCtx w)

√l-string-Iso : (w : String) {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → Iso (Dl-string w B ⊢ A) (B ⊢ √l-string w A)
√l-string-Iso w = √AtIso _⊙_ (suc zero) (leftCtx w)

-- Reindexing is functorial, and commutes with every connective on the
-- nose, since `Dl c A m` is just `A (c ∷ m)`.
Dl-string-map : (w : String) {C : TheoryTy ℓA tt} {D : TheoryTy ℓB tt}
  → C ⊢ D → Dl-string w C ⊢ Dl-string w D
Dl-string-map w f m x = f (w ++ m) x

-- The character-level names from `Grammar.Derivative.Base`.
Dr : Alphabet → TheoryTy ℓA tt → TheoryTy ℓA tt
Dr c = Dr-string (⌈gen c ⌉)

Dl : Alphabet → TheoryTy ℓA tt → TheoryTy ℓA tt
Dl c = Dl-string (⌈gen c ⌉)

√r : Alphabet → TheoryTy ℓA tt → TheoryTy _ tt
√r c = √r-string (⌈gen c ⌉)

√l : Alphabet → TheoryTy ℓA tt → TheoryTy _ tt
√l c = √l-string (⌈gen c ⌉)

-- ...spelled with a cons rather than through `Dl-string-map`, so the index
-- stays syntactically a cons and inference at `Dl c` does not stall.
-- `Regex/Derivative` keeps its own copy: at `roll↑` the implicit carriers
-- resolve only against a locally-defined one.
Dl-map : (c : Alphabet) {C : TheoryTy ℓA tt} {D : TheoryTy ℓB tt}
  → C ⊢ D → Dl c C ⊢ Dl c D
Dl-map c f m x = f (c ∷ m) x
