{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Every test is `refl`, so the typechecker runs the whole composite: the
   guarded fixpoint over the term theory, the node cover, the mode change,
   the OTHER client's guarded fixpoint inside the side condition, the
   projection-fold that reads the substitution off the unification
   derivation, and the soundness proof that turns it into a core term.

   What they exhibit, in order.  That `λx. x` infers `α → α` with no
   annotation anywhere, and that the core term the derivation carries is
   the nameless `λ. 0` -- so a successful run is an elaboration and not a
   report.  That the same holds under binders, under shadowing, and for an
   application whose function is a lambda.  That a free variable resolves
   against an ambient context and takes its type from there.

   Then the two refusals, kept apart on purpose.  A term with an unbound
   variable is refused by the SHAPE mode, which `scopeOnly` observes
   directly; `λx. x x` is accepted by the shape mode and refused by the
   side condition, and the last block localises that refusal all the way
   down to `check` returning `nothing` on the one equation the generated
   stack contains.  The occurs check is not simulated here and it is not
   re-implemented here: it is `Unify/Term`'s, reached through
   `Ans-ofDec`. -}
open import Cubical.Foundations.Prelude
module Theory.Instances.Infer.Tests where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Bool using (Bool ; true ; false)
import Cubical.Data.Sum as Sum

open import Theory.Instances.Infer.Elaborate
import Theory.Instances.Unify.Check as U

idT konst shadow nested appId selfApp openT : RawTm
idT = tlam 0 (tvar 0)
konst = tlam 0 (tlam 1 (tvar 0))
shadow = tlam 0 (tlam 0 (tvar 0))
nested = tlam 0 (tlam 1 (tapp (tvar 0) (tvar 1)))
appId = tapp idT idT
selfApp = tlam 0 (tapp (tvar 0) (tvar 0))
openT = tvar 7


-- INFERENCE, WITH THE ELABORATED CORE TERM ALONGSIDE.  The second
-- component is the type over the unknowns the unifier was left with; the
-- third is `Lambda/Scope`'s nameless syntax, read off the `Lookup` the
-- `var` slot decided.
inf-id : elabTy idT ≡ just (1 , fork (var zero) (var zero) , dlam (dvar 0))
inf-id = refl

inf-konst : elabTy konst
  ≡ just ( 2
         , fork (var (suc zero)) (fork (var zero) (var (suc zero)))
         , dlam (dlam (dvar 1)) )
inf-konst = refl

-- the inner binder wins, in the type as in the index
inf-shadow : elabTy shadow
  ≡ just ( 2
         , fork (var zero) (fork (var (suc zero)) (var (suc zero)))
         , dlam (dlam (dvar 0)) )
inf-shadow = refl

-- λf. λx. f x : (β ⇛ γ) ⇛ β ⇛ γ, with the arrow found by unification and
-- not by a route: nothing in this client ever guesses a type
inf-nested : elabTy nested
  ≡ just ( 2
         , fork (fork (var (suc zero)) (var zero))
                (fork (var (suc zero)) (var zero))
         , dlam (dlam (dapp (dvar 1) (dvar 0))) )
inf-nested = refl

-- an application whose function is a lambda, at the top level
inf-appId : elabTy appId
  ≡ just ( 1
         , fork (var zero) (var zero)
         , dapp (dlam (dvar 0)) (dlam (dvar 0)) )
inf-appId = refl

-- ...and a free variable, against an ambient context: the goal type is an
-- unknown and comes back solved to the context's entry
openG : Goal
openG = 1 , (7 , leaf) ∷ [] , var zero , 1

inf-open : infer openG openT ≡ just (0 , leaf)
inf-open = refl


-- THE OTHER TWO ANSWERS.  Same source text, three backends; at `ND` the
-- answer is a singleton, which is `isPropGen` and `isPropSol` seen from
-- outside.
inf-id-M : inferTyM idT ≡ just (1 , fork (var zero) (var zero))
inf-id-M = refl

inf-id-ND : inferTyND idT ≡ (1 , fork (var zero) (var zero)) ∷ []
inf-id-ND = refl

inf-nested-ND : inferTyND nested
  ≡ (2 , fork (fork (var (suc zero)) (var zero))
             (fork (var (suc zero)) (var zero))) ∷ []
inf-nested-ND = refl


-- REFUSAL ONE: THE SHAPE MODE.  An unbound variable is refused before any
-- constraint is generated, and `scopeOnly` says so by refusing at `genM`.
no-unbound : inferTy openT ≡ nothing
no-unbound = refl

no-unbound-shape : scopeOnly (closed openT) openT ≡ nothing
no-unbound-shape = refl

-- ...and the same run read as a VERDICT.  `shapeVerdict` is total, so the
-- `false` here is `Base`'s `genCell` contraposed -- NO intrinsically typed
-- core term erases to `tvar 7`, at any types over any scope -- and not
-- merely a `nothing` that could have meant the checker gave up.
verdictSide : (i : Goal) → RawTm → Bool
verdictSide i t = Sum.rec (λ _ → true) (λ _ → false) (shapeVerdict i t)

no-unbound-verdict : verdictSide (closed openT) openT ≡ false
no-unbound-verdict = refl

-- ...whereas `λx. x x` is well scoped, which is where the verdict stops
-- and the side condition begins.
selfApp-verdict : verdictSide (closed selfApp) selfApp ≡ true
selfApp-verdict = refl


-- REFUSAL TWO: THE SIDE CONDITION.  `λx. x x` has a perfectly good shape
-- derivation -- every variable is bound -- so the shape mode accepts it,
-- and the whole of the refusal is `Sol`.
selfApp-shape : scopeOnly (closed selfApp) selfApp ≡ just 1
selfApp-shape = refl

no-selfApp : inferTy selfApp ≡ nothing
no-selfApp = refl

no-selfApp-ND : inferTyND selfApp ≡ []
no-selfApp-ND = refl


-- ...AND THE REFUSAL IS THE OCCURS CHECK.  The three equations `λx. x x`
-- generates, verbatim; the unifier's verdict on them; and then the same
-- verdict localised to `Unify/Term`'s `check`, whose ONLY difference from
-- the control below is that the variable being solved for occurs in the
-- term it is being solved to.
selfApp-constraints : gen 4 [] (mvar 4 0) 1 selfApp
  ≡ (var zero , fork (var (suc zero)) (var (suc (suc zero))))
  ∷ (var (suc zero) , fork (var (suc (suc (suc zero)))) (var (suc (suc zero))))
  ∷ (var (suc zero) , var (suc (suc (suc zero))))
  ∷ []
selfApp-constraints = refl

selfApp-unsolvable : U.solve 4 (gen 4 [] (mvar 4 0) 1 selfApp) ≡ nothing
selfApp-unsolvable = refl

-- the equation the machine reaches, and the check that kills it
occurs : U.check {n = 1} zero (fork (var zero) (var (suc zero))) ≡ nothing
occurs = refl

occurs-unify : U.unifyTm 2 (var zero) (fork (var zero) (var (suc zero)))
  ≡ nothing
occurs-unify = refl

-- the control: the same shape with the occurrence removed, and `check`
-- answers
no-occurs : U.check {n = 1} zero (fork (var (suc zero)) (var (suc zero)))
  ≡ just (fork (var zero) (var zero))
no-occurs = refl
