{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- One resolver, two tables, three answers -- and the payoff.

   `T₀` is coherent: at most one `Eq` instance and one `Ord` instance per
   head constructor.  `coh₀` is that fact, `Routed.routed` consumes it, and
   all three answers agree -- `ND` finds exactly one derivation everywhere,
   because a coherent table makes `Resolve` a proposition.

   `T₁` is `T₀` with `instance Eq a => Eq (List a)` declared TWICE, which is
   the smallest possible incoherence and a real one (the same instance
   imported from two modules).  Two things happen, and they are the point:

     * `incoherent` refutes `Coherent T₁`.  So `Routed.routed` cannot be
       applied, and there is no routed resolver for `T₁` -- statically, at
       the type level, not as a failure at run time.  `Dec` has no other
       `Pick`, so an incoherent table has no decision procedure here at all.

     * `Ambiguous.ambig` still applies, because it asks for nothing but a
       covariant answer, and at `ND` it returns BOTH derivations:
       `count₁ eqC (lst ι) ≡ 2`.  That is the incoherence, exhibited as a
       number.  At `Maybe` the same table returns one derivation and says
       nothing about the other -- which is precisely the silent
       instance-selection a PEG-shaped resolver performs.

   Every test is `refl`, so the typechecker runs the resolver. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Cubical.Data.Equality as Eq
module Theory.Instances.Class.ResolveTests where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Sum as Sum

open import Theory.Instances.Class.Resolve
open import Theory.Type.SemanticAction.Base CEqns ⊥ (λ ()) cPresentation

import Theory.Combinator.Answer.Decidable CEqns ⊥ (λ ()) cPresentation as D
import Theory.Combinator.Answer.Incomplete CEqns ⊥ (λ ()) cPresentation as MB
import Theory.Combinator.Answer.NonDet CEqns ⊥ (λ ()) cPresentation as NDm

-- THE COHERENT TABLE.
--
--   instance Eq ι                          -- eqC 0
--   instance Eq a => Eq (List a)           -- eqC 1
--   instance (Eq a, Eq b) => Eq (a ⇒ b)    -- eqC 2
--   instance Ord ι                         -- ordC 0
--   instance Ord a => Ord (List a)         -- ordC 1
--
-- `Ord` has no instance at an arrow, which is what makes the negative
-- tests below interesting rather than vacuous.
T₀ : Table
T₀ .Table.size eqC = 3
T₀ .Table.size ordC = 2
T₀ .Table.head eqC zero = ιOp
T₀ .Table.head eqC (suc zero) = lstOp
T₀ .Table.head eqC (suc (suc zero)) = arrOp
T₀ .Table.head ordC zero = ιOp
T₀ .Table.head ordC (suc zero) = lstOp
T₀ .Table.ctx eqC zero ()
T₀ .Table.ctx eqC (suc zero) _ = eqC
T₀ .Table.ctx eqC (suc (suc zero)) _ = eqC
T₀ .Table.ctx ordC zero ()
T₀ .Table.ctx ordC (suc zero) _ = ordC

coh₀ : Coherent T₀
coh₀ eqC zero zero _ = Eq.refl
coh₀ eqC zero (suc zero) ()
coh₀ eqC zero (suc (suc zero)) ()
coh₀ eqC (suc zero) zero ()
coh₀ eqC (suc zero) (suc zero) _ = Eq.refl
coh₀ eqC (suc zero) (suc (suc zero)) ()
coh₀ eqC (suc (suc zero)) zero ()
coh₀ eqC (suc (suc zero)) (suc zero) ()
coh₀ eqC (suc (suc zero)) (suc (suc zero)) _ = Eq.refl
coh₀ ordC zero zero _ = Eq.refl
coh₀ ordC zero (suc zero) ()
coh₀ ordC (suc zero) zero ()
coh₀ ordC (suc zero) (suc zero) _ = Eq.refl

module R₀ = Resolver T₀
module CD = R₀.Check D.DecAnswer
module CM = R₀.Check MB.MaybeAnswer
module CN = R₀.Check NDm.NDAnswer

-- the same grammar, read three ways, and all three route
module F₀ = R₀.Front coh₀

decRes : CD.Checker R₀.ResSet
decRes = F₀.decRes

mayRes : CM.Checker R₀.ResSet
mayRes = CM.resolver (CM.Routed.routed coh₀ MB.MaybeCommitting)

ndRes : CN.Checker R₀.ResSet
ndRes = CN.resolver (CN.Routed.routed coh₀ NDm.NDCommitting)

decB : Cls → Typ → Bool
decB C t = Sum.rec (λ _ → true) (λ _ → false) (decRes C t tt)

mayB : Cls → Typ → Bool
mayB C t = Sum.rec (λ _ → true) (λ _ → false) (mayRes C t tt)

count : Cls → Typ → ℕ
count C t = length (NDm.ndToList t (ndRes C t tt))

-- ...and the front end: resolve, then read the dictionary off the
-- derivation.  Three internal terms composed, exactly as in
-- `Annotated/Elaborate`'s `compile`.
-- The front end comes from `Resolve`; a test only calls it.
resolve : Cls → Typ → Maybe Dict
resolve = F₀.resolve

-- Positive cases.
dec-eq-ι : decB eqC ι ≡ true
dec-eq-ι = refl

dec-eq-list : decB eqC (lst ι) ≡ true
dec-eq-list = refl

dec-eq-list-list : decB eqC (lst (lst ι)) ≡ true
dec-eq-list-list = refl

dec-eq-arr : decB eqC (ι ⇒ ι) ≡ true
dec-eq-arr = refl

dec-eq-mixed : decB eqC (lst (ι ⇒ lst ι)) ≡ true
dec-eq-mixed = refl

dec-ord-ι : decB ordC ι ≡ true
dec-ord-ι = refl

dec-ord-list : decB ordC (lst (lst ι)) ≡ true
dec-ord-list = refl

-- ...and the negative one: `Ord` has no instance at an arrow, so the
-- premise of `Ord a => Ord (List a)` fails one level down.
dec-ord-arr : decB ordC (ι ⇒ ι) ≡ false
dec-ord-arr = refl

dec-ord-list-arr : decB ordC (lst (ι ⇒ ι)) ≡ false
dec-ord-list-arr = refl

-- `Maybe` agrees.
may-eq-list : mayB eqC (lst (lst ι)) ≡ true
may-eq-list = refl

may-ord-list-arr : mayB ordC (lst (ι ⇒ ι)) ≡ false
may-ord-list-arr = refl

-- `ND` finds exactly one derivation: a coherent table makes `Resolve` a
-- proposition, and the route is what says so.
nd-eq-ι : count eqC ι ≡ 1
nd-eq-ι = refl

nd-eq-list : count eqC (lst (lst ι)) ≡ 1
nd-eq-list = refl

nd-eq-arr : count eqC (lst ι ⇒ ι) ≡ 1
nd-eq-arr = refl

nd-ord-arr : count ordC (ι ⇒ ι) ≡ 0
nd-ord-arr = refl

-- The dictionary, which is the derivation with the proofs erased.
-- `dict n ds` is "instance `n` of this class, applied to `ds`".
dict-eq-ι : resolve eqC ι ≡ just (dict 0 [])
dict-eq-ι = refl

dict-eq-list : resolve eqC (lst ι) ≡ just (dict 1 (dict 0 [] ∷ []))
dict-eq-list = refl

dict-eq-arr : resolve eqC (lst ι ⇒ ι)
            ≡ just (dict 2 (dict 1 (dict 0 [] ∷ []) ∷ dict 0 [] ∷ []))
dict-eq-arr = refl

dict-ord-list : resolve ordC (lst ι) ≡ just (dict 1 (dict 0 [] ∷ []))
dict-ord-list = refl

dict-none : resolve ordC (ι ⇒ ι) ≡ nothing
dict-none = refl


-- THE OVERLAPPING TABLE: `instance Eq a => Eq (List a)`, twice.
T₁ : Table
T₁ .Table.size eqC = 4
T₁ .Table.size ordC = 2
T₁ .Table.head eqC zero = ιOp
T₁ .Table.head eqC (suc zero) = lstOp
T₁ .Table.head eqC (suc (suc zero)) = arrOp
T₁ .Table.head eqC (suc (suc (suc zero))) = lstOp
T₁ .Table.head ordC zero = ιOp
T₁ .Table.head ordC (suc zero) = lstOp
T₁ .Table.ctx eqC zero ()
T₁ .Table.ctx eqC (suc zero) _ = eqC
T₁ .Table.ctx eqC (suc (suc zero)) _ = eqC
T₁ .Table.ctx eqC (suc (suc (suc zero))) _ = eqC
T₁ .Table.ctx ordC zero ()
T₁ .Table.ctx ordC (suc zero) _ = ordC

-- ...and it is not coherent, which is a theorem and not a runtime event.
-- Instances 1 and 3 both have head `lstOp`, so `Route`'s `disjoint` at
-- `just 1` and `just 3` is unprovable and `Routed.routed` does not apply.
incoherent : Coherent T₁ → ⊥
incoherent coh = clash (coh eqC (suc zero) (suc (suc (suc zero))) Eq.refl)
  where
  clash : (Fin.suc Fin.zero Eq.≡ Fin.suc (Fin.suc (Fin.suc Fin.zero))) → ⊥
  clash ()

module R₁ = Resolver T₁
module CN₁ = R₁.Check NDm.NDAnswer
module CM₁ = R₁.Check MB.MaybeAnswer

-- No route, so: enumerate.  `Ambiguous.ambig` needs only a covariant
-- answer -- `Dec` has none, and that is the whole asymmetry.
ndRes₁ : CN₁.Checker R₁.ResSet
ndRes₁ = CN₁.resolver (CN₁.Ambiguous.ambig NDm.NDCov)

mayRes₁ : CM₁.Checker R₁.ResSet
mayRes₁ = CM₁.resolver (CM₁.Ambiguous.ambig MB.MaybeCov)

count₁ : Cls → Typ → ℕ
count₁ C t = length (NDm.ndToList t (ndRes₁ C t tt))

resolve₁ : Cls → Typ → Maybe Dict
resolve₁ C t = Sum.rec (λ d → just (R₁.toDict C t d)) (λ _ → nothing)
  (mayRes₁ C t tt)

-- THE PAYOFF.  Two instances of `Eq (List _)` fire at `List ι`, and `ND`
-- says so.
nd-overlap : count₁ eqC (lst ι) ≡ 2
nd-overlap = refl

-- ...and the ambiguity compounds: `List (List ι)` has two choices at each
-- of two levels.
nd-overlap-nested : count₁ eqC (lst (lst ι)) ≡ 4
nd-overlap-nested = refl

-- Where the table is unambiguous the count is one, so the 2 above is the
-- overlap and not an artefact of enumeration.
nd-overlap-base : count₁ eqC ι ≡ 1
nd-overlap-base = refl

nd-overlap-ord : count₁ ordC (lst (lst ι)) ≡ 1
nd-overlap-ord = refl

-- ...and enumeration agrees with routing on the coherent table, which is
-- the other half of that claim.
module CN₀' = R₀.Check NDm.NDAnswer

countAmb₀ : Cls → Typ → ℕ
countAmb₀ C t = length (NDm.ndToList t
  (CN₀'.resolver (CN₀'.Ambiguous.ambig NDm.NDCov) C t tt))

nd-amb-agrees : countAmb₀ eqC (lst (lst ι)) ≡ 1
nd-amb-agrees = refl

-- `Maybe` on the incoherent table silently takes the first instance that
-- fires and never mentions the second.  This is the failure mode the `ND`
-- run above is diagnosing.
may-overlap : resolve₁ eqC (lst ι) ≡ just (dict 1 (dict 0 [] ∷ []))
may-overlap = refl
