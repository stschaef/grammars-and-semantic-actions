{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- What an intrinsic judgment buys: the elaborator stops being a fold and
   becomes a projection.

   `Der (Γ , A) t` is `Σ[ c ∈ Core Γ A ] (erase c ≡ t)`, so a derivation IS
   a well-typed core term plus the evidence that it is a term for THIS
   source.  Hence:

     elab       = fst   -- and its type says the output is well typed at A
     elabErase  = snd   -- and its type says the output erases to the input

   Neither is a theorem.  The extrinsic version of this file folded a
   derivation into an untyped `CoreTm` and then said nothing whatever about
   the result: "elaboration produces a well-typed term" was a claim about a
   function nobody had checked, and "elaboration preserves the program" was
   not even stated.  Both are now the types of two projections.

   ONE FOLD SURVIVES, and it is worth being exact about which.  `dB` prints
   a core term nameless, replacing each `cvar x v` by `deBruijn Γ A x v`.
   That is a change of variable REPRESENTATION out of a term that is
   already well typed and already pinned to its source; it cannot make an
   ill-typed term, and it is the only thing left that a test could catch
   rather than the typechecker.  Putting numerals into `Core` itself would
   remove it and would cost the judgment its unambiguity -- see `Typing`'s
   note at `cvar`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Annotated.Elaborate where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Sum as Sum

open import Theory.Instances.Annotated.Typing public

open import Theory.Type.SemanticAction.Base
  AEqns ℕ (λ _ → nm) aPresentation
import Theory.Combinator.Answer.Incomplete
  AEqns ℕ (λ _ → nm) aPresentation as MB
import Theory.Combinator.Answer.NonDet
  AEqns ℕ (λ _ → nm) aPresentation as NDm
import Theory.Combinator.Answer.Decidable
  AEqns ℕ (λ _ → nm) aPresentation as D

module CD = Check D.DecAnswer
module CM = Check MB.MaybeAnswer
module CN = Check NDm.NDAnswer

-- Elaboration, and its two correctness statements, all three definitional.
elab : (i : Jdg) (t : ATm) → Der i t → Core (i .fst) (i .snd)
elab i t d = d .fst

elabErase : (i : Jdg) (t : ATm) (d : Der i t) → erase (elab i t d) ≡ t
elabErase i t d = d .snd

-- The nameless printout: `Core` resolves a variable by a `Lookup`, and the
-- de Bruijn index is the number of "not here" steps in it.  The search
-- happened once, in the checker; this only counts.
data Nameless : Type ℓ-zero where
  dvar : ℕ → Nameless
  dapp : Nameless → Nameless → Nameless
  dlam : Ty → Nameless → Nameless

dB : {Γ : Ctx} {A : Ty} → Core Γ A → Nameless
dB (cvar {Γ = Γ} {A = A} x v) = dvar (deBruijn Γ A x v)
dB (capp f a) = dapp (dB f) (dB a)
dB (clam {B = B} x c) = dlam B (dB c)

-- ...as a semantic action, which is the DSL's own name for a readout: a
-- map from a grammar into a constant `Δ X`.  Stating it this way is not
-- decoration -- it is what lets `semact-dec` and `observe` below do the
-- rest, so the boundary between "internal term" and "external value" is
-- crossed exactly once, in `observe`, rather than by hand.
elabAction : (i : Jdg) → SemanticAction (Der i) Nameless
elabAction i t d = dB (elab i t d) , tt

-- Check, then read out.  The front end is a composition of three internal
-- terms: the checker `⊤Ty ⊢ DecTy (Der i)`, the action that `semact-dec`
-- builds from `elabAction`, and `observe`, which is the one place a
-- `⊤Ty`-map is read.
compile : (Γ : Ctx) (A : Ty) → ATm → Maybe Nameless
compile Γ A = observe (CD.typed (Γ , A)) (semact-dec (elabAction (Γ , A)))

-- THE SAME ACTION AT THE OTHER TWO ANSWERS.  All three are available here,
-- and the third is the one worth having: `observeND` applies the action
-- under the list, so `compileAll` returns every core term the checker can
-- build for a source term.  That is the empirical form of `isPropDer` --
-- the proof says two derivations are equal, the list says how many the
-- checker constructs -- and it is the measurement that would expose an
-- intrinsic syntax whose erasure is not injective.  See the `shadow` test.
compileM : (Γ : Ctx) (A : Ty) → ATm → Maybe Nameless
compileM Γ A = observe (CM.typed (Γ , A)) (semact-Maybe (elabAction (Γ , A)))

compileAll : (Γ : Ctx) (A : Ty) → ATm → List Nameless
compileAll Γ A = NDm.observeND (CN.typed (Γ , A)) (elabAction (Γ , A))
-- Tests.  `refl` again, so the typechecker runs the whole front end.

idT : ATm
idT = alam 0 ι (avar 0)

konst : ATm                             -- λx:ι. λy:ι. x
konst = alam 0 ι (alam 1 ι (avar 0))

shadow : ATm                            -- λx:ι. λx:ι. x
shadow = alam 0 ι (alam 0 ι (avar 0))

nested : ATm                            -- λf:ι⇒ι. λx:ι. f x
nested = alam 0 (ι ⇒ ι) (alam 1 ι (aapp ι (avar 0) (avar 1)))

elab-id : compile [] (ι ⇒ ι) idT ≡ just (dlam ι (dvar 0))
elab-id = refl

-- the outer binder, so index 1: the projection read this off the core term
elab-konst : compile [] (ι ⇒ ι ⇒ ι) konst ≡ just (dlam ι (dlam ι (dvar 1)))
elab-konst = refl

-- ...and shadowing resolves inward, so the *same* source name gives 0
elab-shadow : compile [] (ι ⇒ ι ⇒ ι) shadow ≡ just (dlam ι (dlam ι (dvar 0)))
elab-shadow = refl

elab-nested : compile [] ((ι ⇒ ι) ⇒ ι ⇒ ι) nested
            ≡ just (dlam (ι ⇒ ι) (dlam ι (dapp (dvar 1) (dvar 0))))
elab-nested = refl

-- a free variable resolves against the ambient context
elab-open : compile ((7 , ι) ∷ []) ι (avar 7) ≡ just (dvar 0)
elab-open = refl

elab-open2 : compile ((3 , ι) ∷ (7 , ι) ∷ []) ι (avar 7) ≡ just (dvar 1)
elab-open2 = refl

-- ill-typed terms produce nothing, not a bad core term
elab-bad : compile [] ι idT ≡ nothing
elab-bad = refl

-- `Maybe` commits to the first alternative and here there is only one, so
-- it agrees with the decision on every term above.
may-nested : compileM [] ((ι ⇒ ι) ⇒ ι ⇒ ι) nested
           ≡ just (dlam (ι ⇒ ι) (dlam ι (dapp (dvar 1) (dvar 0))))
may-nested = refl

may-bad : compileM [] ι idT ≡ nothing
may-bad = refl

-- ...and `ND` builds exactly one core term, so the intrinsic judgment is
-- unambiguous in fact and not only in the retraction proof.
all-id : compileAll [] (ι ⇒ ι) idT ≡ dlam ι (dvar 0) ∷ []
all-id = refl

-- the case the erasure fibre could have got wrong: two bindings of the
-- name 0, one core term.  A `cvar` holding a bare numeral would list two.
all-shadow : compileAll [] (ι ⇒ ι ⇒ ι) shadow ≡ dlam ι (dlam ι (dvar 0)) ∷ []
all-shadow = refl

all-nested : compileAll [] ((ι ⇒ ι) ⇒ ι ⇒ ι) nested
           ≡ dlam (ι ⇒ ι) (dlam ι (dapp (dvar 1) (dvar 0))) ∷ []
all-nested = refl

all-bad : compileAll [] ι idT ≡ []
all-bad = refl
