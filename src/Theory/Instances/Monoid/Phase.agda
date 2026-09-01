{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A phase is a semantic action from a grammar into the free monoid of the next
   alphabet (not a theory morphism: lexing is neither per-letter nor total).
   KNOWN GAPS (Dyck pilot): `Gr` must be TOTAL over the input (no residue, no
   prefix-consuming phase); no phase composition -- joining is metalanguage
   `Maybe`-bind, which forgets which phase failed. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Phase
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Maybe as Mb
import Cubical.Data.Equality as Eq
import Agda.Builtin.String as AS

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Type.Decidable.Base MonEqns Alphabet (λ _ → tt)
  listPresentation
open import Theory.Type.SemanticAction.Base MonEqns Alphabet (λ _ → tt)
  listPresentation

private variable ℓA ℓO ℓX : Level

record Phase (ℓA : Level) (Out : Type ℓO) : Type (ℓ-max (ℓ-suc (ℓ-max ℓA ℓO)) ℓM) where
  field
    Gr : TheoryTy ℓA tt
    dec : Decidable Gr
    emit : SemanticAction Gr (List Out)

-- The display boundary: the only place a parse becomes metalanguage data.

runPhase : {Out : Type ℓO} (P : Phase ℓA Out)
  → String → Mb.Maybe (List Out)
runPhase P w = observe (Phase.dec P) (semact-dec (Phase.emit P)) w

-- Instance-resolved, so a test can only print what the grammar actually says.

record Display (A : TheoryTy ℓA tt) : Type (ℓ-max ℓA ℓM) where
  field shown : SemanticAction A AS.String

open Display {{...}} public
