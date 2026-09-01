{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Instances.Monoid.Strings.Base
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

private variable ℓA ℓB ℓC ℓD ℓY : Level

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Unit using (Unit ; tt ; Unit* ; tt*)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; ++-assoc ; ++-unit-r)
import Cubical.Data.List as L
import Cubical.Data.Empty as Emp
import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq
open import Cubical.Data.Equality.More using (isSet→isSetEq)

open import Cubical.WildCat.LocallySmall.Base

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.ListPresentation Alphabet isSetAlphabet
  using (listPresentation) public

open import Theory.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Lift.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Sum.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Sum.Binary.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Operation.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Inductive.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Top.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Bottom.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Product.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Product.Binary.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Function.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Equalizer.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Distributivity MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Later.Derivative MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Unambiguity.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.HLevels MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Inductive.HLevels MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Top.Properties MonEqns Alphabet (λ _ → tt) listPresentation

open WildCatNotation
open WildCatIso

String : Type ℓM
String = ↓M tt

char : TheoryTy ℓM tt
char = ⊕[ c ∈ Alphabet ] ⌈ ⌈gen c ⌉ ⌉

εTy : TheoryTy ℓM tt
εTy = ⊗[ ε· ][ (λ ()) ] tt*
