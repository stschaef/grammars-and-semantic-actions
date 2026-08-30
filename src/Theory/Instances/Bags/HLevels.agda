{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Set-ness of the bag types.  `löb` fixes a family and wants it
   set-valued, so every guarded fold over `Seq` or `Sorted` pays here. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Equality as Eq
open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open SortedSig
open SortedEqns
module Theory.Instances.Bags.HLevels
  (El : Type ℓ-zero) (isSetEl : isSet El) where

open import Cubical.Data.Unit using (Unit ; tt ; tt*)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Bags.Base El
open import Theory.Instances.Bags.Sequence El
open import Theory.Type.HLevels BagEqns El (λ _ → tt) closingPresentation
open import Theory.Type.Inductive.HLevels BagEqns El (λ _ → tt)
  closingPresentation

-- a representable is an equality in a set
isSet⌈⌉ : (a : Bag) → isSetTheoryTy ⌈ a ⌉
isSet⌈⌉ a m =
  isProp→isSet
    (isOfHLevelRetractFromIso 1 (invIso Eq.PathIsoEq) (M .fst tt .snd _ _))

isSetεB : isSetTheoryTy εB
isSetεB = isSet⊗ ε· (λ ()) tt* λ ()

isSetValuedSeqCode : isSetValued {X = Unit} {xs = λ _ → tt} SeqCode
isSetValuedSeqCode =
  lift isSetBool , λ where
    false → lift isSetεB
    true → lift isSetEl , λ x → two (lift (isSet⌈⌉ ⌈gen x ⌉)) (lift tt*)

isSet⊎B : {ℓA ℓB : Level} {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → isSetTheoryTy A → isSetTheoryTy B → isSetTheoryTy (A ⊎B B)
isSet⊎B {A = A} {B = B} isSetA isSetB =
  isSet⊗ _⊙_ (two _ _) (A , B , tt*) λ where
    zero → isSetA
    (suc zero) → isSetB

-- `⊸B` is a nested Π, so its set-ness is its codomain's.
isSet⊸B : {ℓA ℓB : Level} {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → isSetTheoryTy B → isSetTheoryTy (A ⊸B B)
isSet⊸B isSetB m =
  isSetΠ λ _ → isSetΠ λ _ → isSetΠ λ z → isSetΠ λ _ → isSetΠ λ _ → isSetB z

isSetSeq : isSetTheoryTy Seq
isSetSeq = isSetμ (λ _ → SeqCode) (λ _ → isSetValuedSeqCode) tt
