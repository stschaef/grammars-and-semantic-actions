{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The suffix order's memo chain, and the tabulated Löb it justifies.

   `Suffix/Base`'s `Guarded▷` is `löbFrom`, whose hypothesis is a presheaf
   hom: reading it at a suffix re-derives the value there.  `Later/
   Tabulated` materialises it instead, and asks only for a `Chain` -- the
   points below each point, growing by one cell per step.  For the
   proper-suffix order that is the list of a word's proper suffixes.

   This belongs in `Suffix/`, next to the order it is about. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Automaton.SuffixChain
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Suffix.Base Alphabet isSetAlphabet
  using (_◂_ ; SPt ; SFam ; Below ; suffixOrder)
open import Theory.Type.Later.Tabulated MonEqns Alphabet (λ _ → tt)
  listPresentation
open import Theory.Type.Guarded.Base MonEqns Alphabet (λ _ → tt)
  listPresentation using (Löb)
open import Theory.Type.Guarded.Justification MonEqns Alphabet (λ _ → tt)
  listPresentation using (löbMemo)

private
  -- nearest first
  suffixes : SPt → List SPt
  suffixes (x , []) = []
  suffixes (x , c ∷ v) = (x , v) ∷ suffixes (x , v)

  findSuf : (p q : SPt) → Below q p → q ∈ᴾ suffixes p
  findSuf (x , []) q lt = Empty.rec (lt .lower)
  findSuf (x , c ∷ v) (y , u) (Sum.inl Eq.refl) = here
  findSuf (x , c ∷ v) q (Sum.inr i) = there (findSuf (x , v) q i)

  viewSuf : (p : SPt) → ChainView (λ _ → tt) suffixOrder suffixes p
  viewSuf (x , []) = minimal Eq.refl
  viewSuf (x , c ∷ v) = extends (x , v) (Sum.inl Eq.refl) Eq.refl

suffixChain : Chain (λ _ → tt) suffixOrder
suffixChain = record
  { below = suffixes
  ; find = λ {p} {q} lt → findSuf p q lt
  ; view = viewSuf }

-- `Suffix/Base`'s `Guarded▷`, memoised: same `▷`, same `app`, same value
-- (`löbMemo≡löbFrom`), one evaluation per suffix.
module GuardedMemo▷ {ℓA} (A : SFam ℓA) (isSetA : ∀ x m → isSet (A x m)) where
  suffixLöbMemo : Löb Below A
  suffixLöbMemo = löbMemo suffixOrder suffixChain (λ r → r) A isSetA

  open Löb suffixLöbMemo public
