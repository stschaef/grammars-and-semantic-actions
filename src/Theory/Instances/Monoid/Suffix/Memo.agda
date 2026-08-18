{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Memoisation for the suffix order: its downsets are chains, so the
   tabulated later modality applies and a parser's memo table is one cell
   per suffix.  This is an optimisation layer -- `Packrat.agda` parses
   without it. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Suffix.Memo
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Sum as Sum
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Suffix.Base Alphabet isSetAlphabet
import Theory.Instances.Monoid.Suffix.Base Alphabet isSetAlphabet as S
open import Theory.Type.Later.Indexed MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Later.Tabulated MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Guarded.Base MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Guarded.Justification MonEqns Alphabet (λ _ → tt)
  listPresentation

-- the memo row addresses below a string: its proper suffixes, longest first
suffixes : String → List SPt
suffixes [] = []
suffixes (c ∷ w) = (tt , w) ∷ suffixes w

_∈ˢ_ : SPt → List SPt → Type ℓAlph
p ∈ˢ ps = _∈ᴾ_ {X = Unit} {xs = λ _ → tt} p ps

private
  findSuffix : ∀ {w} v → w ◂ v → (tt , w) ∈ˢ suffixes v
  findSuffix (c ∷ v) (Sum.inl Eq.refl) = here
  findSuffix (c ∷ v) (Sum.inr i) = there (findSuffix v i)

suffixChain : Chain (λ _ → tt) suffixOrder
suffixChain .Chain.below p = suffixes (p .snd)
suffixChain .Chain.find {p = p} lt = findSuffix (p .snd) lt
suffixChain .Chain.view (x , []) = minimal Eq.refl
suffixChain .Chain.view (x , c ∷ w) = extends (tt , w) (Sum.inl Eq.refl) Eq.refl

-- The packrat memo table for a family of results, one row per suffix.  Its
-- `▷` is the plain one, so a consumer writes a single step and chooses;
-- `agree` says the choice does not change the answer.
module GuardedMemo▷ {ℓA : Level} (A : SFam ℓA)
  (isSetA : ∀ x m → isSet (A x m)) where
  memoLöb : Löb Below A
  memoLöb = löbMemo suffixOrder suffixChain (λ r → r) A isSetA

  open Löb memoLöb public

  agree : (φ : ∀ x → Löb.▷ memoLöb x ⊢ A x)
    → löb φ ≡ Löb.löb (S.Guarded▷.suffixLöb A isSetA) φ
  agree = löbMemo≡löbFrom suffixOrder suffixChain (λ r → r) A isSetA
