{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The interface between front-end phases.

   Every phase reads a word over its own alphabet and writes a word over
   the next one.  Both live in the theory of monoids -- phase `n` in
   `Mon + Th(Aₙ)`, phase `n+1` in `Mon + Th(Aₙ₊₁)` -- so the *codomain*
   shift is a change of theory.

   The map is not.  A morphism `Mon + Th(X) → Mon + Th(Y)` comes from a
   function `X → List Y` and is therefore a monoid homomorphism
   `List X → List Y`, i.e. a per-letter translation.  Lexing is neither:
   maximal munch depends on what follows (`where` in `wherever` is not a
   keyword), and it is partial (`"?"` lexes to nothing).

   So a phase transition is not a theory morphism.  It is a semantic
   action out of a grammar in one theory into the free monoid of the
   next: theory morphisms move grammars covariantly, phase transitions
   move *parses* into *words*.  That is what `Phase` records.

       Phase Out = a grammar over this alphabet
                 + a decision for it
                 + an emission into `List Out`

   and `Parse (lex s)` is `run` of one phase fed to `run` of the next. -}
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

------------------------------------------------------------------------
-- A phase.

record Phase (ℓA : Level) (Out : Type ℓO) : Type (ℓ-max (ℓ-suc (ℓ-max ℓA ℓO)) ℓM) where
  field
    -- what this phase recognises, over *this* alphabet
    Gr : TheoryTy ℓA tt
    -- ...decided, so a failure is a refutation and not a dropped error
    dec : Decidable Gr
    -- ...and what it hands the next phase: a word over the next alphabet
    emit : SemanticAction Gr (List Out)

------------------------------------------------------------------------
-- Running one.
--
-- This is the display boundary, and the only place a parse becomes
-- metalanguage data: `observe` applies the semantic action to whatever
-- the decision found.  Everything above it is `⊢`-terms.

runPhase : {Out : Type ℓO} (P : Phase ℓA Out)
  → String → Mb.Maybe (List Out)
runPhase P w = observe (Phase.dec P) (semact-dec (Phase.emit P)) w

------------------------------------------------------------------------
-- A canonical semantic action, for readable tests.
--
-- Instance-resolved, so a test says `display (run p input)` rather than
-- reaching into the parse by hand; the point is that a test can only
-- print what the grammar actually says.

record Display (A : TheoryTy ℓA tt) : Type (ℓ-max ℓA ℓM) where
  field shown : SemanticAction A AS.String

open Display {{...}} public

displayOf : {A : TheoryTy ℓA tt} → {{Display A}} → SemanticAction A AS.String
displayOf {{d}} = Display.shown d
