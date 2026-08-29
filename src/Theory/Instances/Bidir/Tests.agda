{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Every test is `refl`, so the typechecker runs the whole front end: the
   guarded fixpoint, the node cover, both routes, and the fold.

   What they exhibit, in order: that an application whose function is a
   lambda both checks and synthesises even though the node carries no
   annotation; that the elaborated output is the `Annotated` term, with the
   annotation the route recovered, and that `Annotated`'s own checker
   accepts it; that a term with no type lands in the `nothing` cell of the
   route rather than failing; that the synthesis mode -- which calls the
   checking mode at the same term, on the guard's rank rather than on the
   subterm order -- terminates and agrees; and that at `ND` every answer is
   a singleton, which is `isPropChk` observed from outside. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Bidir.Tests where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (_,_)

open import Theory.Instances.Bidir.Elaborate
import Theory.Instances.Annotated.Elaborate as AE

-- λx:ι. x
idT : BTm
idT = blam 0 ι (bvar 0)

-- λx:ι. λy:ι. x
konst : BTm
konst = blam 0 ι (blam 1 ι (bvar 0))

-- λf:ι⇒ι. λx:ι. f x   -- the application node carries nothing
nested : BTm
nested = blam 0 (ι ⇒ ι) (blam 1 ι (bapp (bvar 0) (bvar 1)))

Γ₁ : Ctx
Γ₁ = (1 , ι) ∷ []

-- an application whose function is a lambda: no annotation on the node,
-- and the argument type is found by the route
beta : BTm
beta = bapp idT (bvar 1)

-- CHECKING.
chk-id : check [] (ι ⇒ ι) idT ≡ just (alam 0 ι (avar 0))
chk-id = refl

chk-beta : check Γ₁ ι beta ≡ just (aapp ι (alam 0 ι (avar 0)) (avar 1))
chk-beta = refl

-- SYNTHESIS.  The mode change: `Syn` at a term is the sum, over every
-- type, of `Chk` at that same term, and the guard's rank is what makes the
-- call legal.
syn-id : synth [] idT ≡ just (ι ⇒ ι , alam 0 ι (avar 0))
syn-id = refl

syn-beta : synth Γ₁ beta ≡ just (ι , aapp ι (alam 0 ι (avar 0)) (avar 1))
syn-beta = refl

syn-konst : synth [] konst ≡ just (ι ⇒ ι ⇒ ι , alam 0 ι (alam 1 ι (avar 0)))
syn-konst = refl

syn-nested : synth [] nested
  ≡ just ((ι ⇒ ι) ⇒ ι ⇒ ι
         , alam 0 (ι ⇒ ι) (alam 1 ι (aapp ι (avar 0) (avar 1))))
syn-nested = refl

-- ...and a free variable resolves against the ambient context
syn-open : synth Γ₁ (bvar 1) ≡ just (ι , avar 1)
syn-open = refl

-- THE `nothing` CELL.  Not a failure of the checker: the route's cover
-- lands the term in the unnamed cell, and `routeIn` refutes the whole sum
-- from the cover's `disjoint`.
syn-unbound : synth [] (bvar 5) ≡ nothing
syn-unbound = refl

-- applying something whose type is not an arrow: the function synthesises
-- `ι`, the candidate for the application is `nothing`
syn-notfun : synth ((0 , ι) ∷ []) (bapp (bvar 0) (bvar 0)) ≡ nothing
syn-notfun = refl

-- ...and a lambda whose body has no type has none either: the `nothing`
-- cell reached through a premise rather than at the node itself.  With
-- `lamOp` still annotated, a lambda that DOES have a type always
-- synthesises it -- checking never succeeds where synthesis fails, so the
-- `nothing` cell is exactly ill-typedness.
syn-badlam : synth [] (blam 0 ι (bapp (bvar 0) (bvar 0))) ≡ nothing
syn-badlam = refl

-- ILL-TYPED terms are rejected rather than elaborated badly.
chk-bad : check [] ι idT ≡ nothing
chk-bad = refl

chk-badarg : check Γ₁ ι (bapp idT idT) ≡ nothing
chk-badarg = refl

-- ...and checking against the wrong type of a well-typed term
chk-mismatch : check Γ₁ (ι ⇒ ι) beta ≡ nothing
chk-mismatch = refl

-- THE ANNOTATION IS RECOVERED.  The output of the unannotated checker is
-- an `Annotated` term, and `Annotated`'s own checker accepts it: the
-- composition below is bidirectional checking, then annotated checking,
-- then elaboration to the core language.
private
  thenAnnotated : (Γ : Ctx) (A : Ty) → Maybe ATm → Maybe AE.CoreTm
  thenAnnotated Γ A nothing = nothing
  thenAnnotated Γ A (just t) = AE.compile Γ A t

roundtrip-beta : thenAnnotated Γ₁ ι (check Γ₁ ι beta)
  ≡ just (AE.capp (AE.clam ι (AE.cvar 0)) (AE.cvar 0))
roundtrip-beta = refl

roundtrip-nested : thenAnnotated [] ((ι ⇒ ι) ⇒ ι ⇒ ι) (check [] ((ι ⇒ ι) ⇒ ι ⇒ ι) nested)
  ≡ just (AE.clam (ι ⇒ ι) (AE.clam ι (AE.capp (AE.cvar 1) (AE.cvar 0))))
roundtrip-nested = refl

-- THE OTHER TWO ANSWERS.  `Maybe` routes through `FromCov.committing`
-- rather than through `routeIn`, and agrees.
chkM-beta : checkM Γ₁ ι beta ≡ just (aapp ι (alam 0 ι (avar 0)) (avar 1))
chkM-beta = refl

synM-nested : synthM [] nested
  ≡ just ((ι ⇒ ι) ⇒ ι ⇒ ι
         , alam 0 (ι ⇒ ι) (alam 1 ι (aapp ι (avar 0) (avar 1))))
synM-nested = refl

chkM-bad : checkM [] ι idT ≡ nothing
chkM-bad = refl

-- `ND` keeps every derivation, so a singleton is unambiguity, observed.
-- The route's `disjoint` is what makes it one and not several: every
-- alternative but the named one contributes the empty answer.
chkND-beta : checkND Γ₁ ι beta ≡ aapp ι (alam 0 ι (avar 0)) (avar 1) ∷ []
chkND-beta = refl

synND-beta : synthND Γ₁ beta ≡ (ι , aapp ι (alam 0 ι (avar 0)) (avar 1)) ∷ []
synND-beta = refl

synND-nested : synthND [] nested
  ≡ ((ι ⇒ ι) ⇒ ι ⇒ ι
    , alam 0 (ι ⇒ ι) (alam 1 ι (aapp ι (avar 0) (avar 1)))) ∷ []
synND-nested = refl

chkND-bad : checkND [] ι idT ≡ []
chkND-bad = refl

synND-unbound : synthND [] (bvar 5) ≡ []
synND-unbound = refl
