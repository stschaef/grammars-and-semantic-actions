{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The interface between front-end phases: each phase reads a word over its
   own alphabet and writes a word over the next.

   The change of alphabet is a change of theory, but the map is not a theory
   morphism.  A morphism `Mon + Th(X) → Mon + Th(Y)` comes from a function
   `X → List Y`, hence is a per-letter and total translation
   `List X → List Y`.  Lexing is neither: maximal munch depends on what
   follows (`where` inside `wherever` is not a keyword), and it is partial
   (`"?"` lexes to nothing).  A phase is therefore a semantic action out of a
   type in one theory into the free monoid of the next: it moves *parses* to
   *words*, where a theory morphism moves types to types.

   Two side conditions.  `Ty` must be total over the input: `runPhase`
   observes at the whole word, so there is no residue and no phase that
   consumes a prefix.  And there is no composition, so the last phase of a
   pipeline is not a `Phase` -- it emits a parse tree rather than a word --
   and joining two phases is metalanguage `Maybe`-bind, which flattens
   *which* phase failed. -}
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
    Ty : TheoryTy ℓA tt
    dec : Decidable Ty
    emit : SemanticAction Ty (List Out)

-- The only place a parse becomes metalanguage data; everything above it is
-- `⊢`-terms.

runPhase : {Out : Type ℓO} (P : Phase ℓA Out)
  → String → Mb.Maybe (List Out)
runPhase P w = observe (Phase.dec P) (semact-dec (Phase.emit P)) w

-- Instance-resolved, so a test can only print what the grammar actually
-- says rather than reaching into the parse by hand.

record Display (A : TheoryTy ℓA tt) : Type (ℓ-max ℓA ℓM) where
  field shown : SemanticAction A AS.String

open Display {{...}} public

displayOf : {A : TheoryTy ℓA tt} → {{Display A}} → SemanticAction A AS.String
displayOf {{d}} = Display.shown d
