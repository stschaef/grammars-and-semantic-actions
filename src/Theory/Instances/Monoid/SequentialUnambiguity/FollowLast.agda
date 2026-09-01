{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Follow-last sets, as refutations.  The primed version (Brüggemann-Klein and Wood;
   also Krishnaswami and Yallop) restricts the left factor to nonempty words;
   the two agree when `A` is non-nullable. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.SequentialUnambiguity.FollowLast
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Sum as Sum

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (&⊕-distR ; ⊗ε-unit-l⁻)
open import Theory.Instances.Monoid.SequentialUnambiguity.First
  Alphabet isSetAlphabet public

private variable ℓA ℓB ℓC : Level

FollowLastTy : TheoryTy ℓA tt → Alphabet → TheoryTy _ tt
FollowLastTy A c = (A ⊗ startsWith c) & A

FollowLastTy' : TheoryTy ℓA tt → Alphabet → TheoryTy _ tt
FollowLastTy' A c = ((A & char⁺) ⊗ startsWith c) & A

_∉FollowLast_ : Alphabet → TheoryTy ℓA tt → Type _
c ∉FollowLast A = FollowLastTy A c ⊢ ⊥Ty

_∉FollowLast'_ : Alphabet → TheoryTy ℓA tt → Type _
c ∉FollowLast' A = FollowLastTy' A c ⊢ ⊥Ty

FollowLastTy'→FollowLastTy : {A : TheoryTy ℓA tt} {c : Alphabet}
  → FollowLastTy' A c ⊢ FollowLastTy A c
FollowLastTy'→FollowLastTy = (⊗-map π₁ id⊢) ,&p id⊢

∉FollowLast→∉FollowLast' : {A : TheoryTy ℓA tt} {c : Alphabet}
  → c ∉FollowLast A → c ∉FollowLast' A
∉FollowLast→∉FollowLast' h = h ∘⊢ FollowLastTy'→FollowLastTy

-- converse needs `A` non-nullable: only then is every `A` a nonempty `A`
∉FollowLast'→∉FollowLast : {A : TheoryTy ℓA tt} {c : Alphabet}
  → ¬Nullable A → c ∉FollowLast' A → c ∉FollowLast A
∉FollowLast'→∉FollowLast nu h =
  h ∘⊢ (⊗-map (id⊢ ,& ¬Nullable→char⁺ nu) id⊢ ,&p id⊢)

∉FollowLast∘⊢ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {c : Alphabet}
  → (f : A ⊢ B) → c ∉FollowLast B → c ∉FollowLast A
∉FollowLast∘⊢ f h = h ∘⊢ (⊗-map f id⊢ ,&p f)

-- take the empty word as the left factor
∉FollowLast→∉First : {A : TheoryTy ℓA tt} {c : Alphabet}
  → εTy ⊢ A → c ∉FollowLast A → c ∉First A
∉FollowLast→∉First null h =
  h ∘⊢ ((⊗-map null id⊢ ∘⊢ ⊗ε-unit-l⁻) ,&p id⊢)

FollowLastTy-split : {A : TheoryTy ℓA tt} {c : Alphabet}
  → FollowLastTy A c ⊢ ((A ⊗ startsWith c) & (A & εTy))
                     ⊕ ((A ⊗ startsWith c) & (A & char⁺))
FollowLastTy-split = &⊕-distR ∘⊢ (π₁ ,& (stringSplit ∘⊢ π₂))
