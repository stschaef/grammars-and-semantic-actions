{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Every test is `refl`, so the typechecker runs the whole front end: the
   guarded fixpoint, the node cover, both routes, and the fold. -}
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

-- application of a lambda: the argument type is found by the route
beta : BTm
beta = bapp idT (bvar 1)

chk-id : check [] (ι ⇒ ι) idT ≡ just (alam 0 ι (avar 0))
chk-id = refl

chk-beta : check Γ₁ ι beta ≡ just (aapp ι (alam 0 ι (avar 0)) (avar 1))
chk-beta = refl

-- `Syn` is the sum over types of `Chk`; the guard's rank legalises the call
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

-- a free variable resolves against the ambient context
syn-open : synth Γ₁ (bvar 1) ≡ just (ι , avar 1)
syn-open = refl

-- `nothing` is not checker failure: the cover lands the term in the
-- unnamed cell and `routeIn` refutes the sum via `disjoint`
syn-unbound : synth [] (bvar 5) ≡ nothing
syn-unbound = refl

-- applying a non-arrow: the function synthesises `ι`, candidate `nothing`
syn-notfun : synth ((0 , ι) ∷ []) (bapp (bvar 0) (bvar 0)) ≡ nothing
syn-notfun = refl

-- `nothing` reached through a premise; with `lamOp` annotated, checking
-- never succeeds where synthesis fails, so `nothing` is exactly
-- ill-typedness
syn-badlam : synth [] (blam 0 ι (bapp (bvar 0) (bvar 0))) ≡ nothing
syn-badlam = refl

-- ill-typed terms are rejected, not elaborated badly
chk-bad : check [] ι idT ≡ nothing
chk-bad = refl

chk-badarg : check Γ₁ ι (bapp idT idT) ≡ nothing
chk-badarg = refl

-- checking a well-typed term against the wrong type
chk-mismatch : check Γ₁ (ι ⇒ ι) beta ≡ nothing
chk-mismatch = refl

-- the unannotated checker outputs an `Annotated` term its checker accepts
private
  thenAnnotated : (Γ : Ctx) (A : Ty) → Maybe ATm → Maybe AE.Nameless
  thenAnnotated Γ A nothing = nothing
  thenAnnotated Γ A (just t) = AE.compile Γ A t

roundtrip-beta : thenAnnotated Γ₁ ι (check Γ₁ ι beta)
  ≡ just (AE.dapp (AE.dlam ι (AE.dvar 0)) (AE.dvar 0))
roundtrip-beta = refl

roundtrip-nested : thenAnnotated [] ((ι ⇒ ι) ⇒ ι ⇒ ι) (check [] ((ι ⇒ ι) ⇒ ι ⇒ ι) nested)
  ≡ just (AE.dlam (ι ⇒ ι) (AE.dlam ι (AE.dapp (AE.dvar 1) (AE.dvar 0))))
roundtrip-nested = refl

-- `Maybe` routes through `FromCov.committing`, not `routeIn`, and agrees
chkM-beta : checkM Γ₁ ι beta ≡ just (aapp ι (alam 0 ι (avar 0)) (avar 1))
chkM-beta = refl

synM-nested : synthM [] nested
  ≡ just ((ι ⇒ ι) ⇒ ι ⇒ ι
         , alam 0 (ι ⇒ ι) (alam 1 ι (aapp ι (avar 0) (avar 1))))
synM-nested = refl

chkM-bad : checkM [] ι idT ≡ nothing
chkM-bad = refl

-- `ND` keeps every derivation: a singleton is observed unambiguity, by
-- the route's `disjoint`
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
