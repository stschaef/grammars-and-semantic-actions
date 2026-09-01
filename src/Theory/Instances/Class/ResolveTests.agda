{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `T₀` coherent: `Routed.routed` applies, `ND` finds one derivation.
   `T₁` overlaps: `incoherent` refutes `Coherent T₁` statically;
   `Ambiguous.ambig` at `ND` counts both.  Every test is `refl`. -}
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

--   instance Eq ι                          -- eqC 0
--   instance Eq a => Eq (List a)           -- eqC 1
--   instance (Eq a, Eq b) => Eq (a ⇒ b)    -- eqC 2
--   instance Ord ι                         -- ordC 0
--   instance Ord a => Ord (List a)         -- ordC 1
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

resolve : Cls → Typ → Maybe Dict
resolve = F₀.resolve

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

dec-ord-arr : decB ordC (ι ⇒ ι) ≡ false
dec-ord-arr = refl

dec-ord-list-arr : decB ordC (lst (ι ⇒ ι)) ≡ false
dec-ord-list-arr = refl

may-eq-list : mayB eqC (lst (lst ι)) ≡ true
may-eq-list = refl

may-ord-list-arr : mayB ordC (lst (ι ⇒ ι)) ≡ false
may-ord-list-arr = refl

nd-eq-ι : count eqC ι ≡ 1
nd-eq-ι = refl

nd-eq-list : count eqC (lst (lst ι)) ≡ 1
nd-eq-list = refl

nd-eq-arr : count eqC (lst ι ⇒ ι) ≡ 1
nd-eq-arr = refl

nd-ord-arr : count ordC (ι ⇒ ι) ≡ 0
nd-ord-arr = refl

-- `dict n ds` = instance `n` of the class, applied to `ds`.
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


-- `T₁`: `instance Eq a => Eq (List a)`, twice.
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

-- Instances 1 and 3 share head `lstOp`, so `Route`'s `disjoint` is unprovable.
incoherent : Coherent T₁ → ⊥
incoherent coh = clash (coh eqC (suc zero) (suc (suc (suc zero))) Eq.refl)
  where
  clash : (Fin.suc Fin.zero Eq.≡ Fin.suc (Fin.suc (Fin.suc Fin.zero))) → ⊥
  clash ()

module R₁ = Resolver T₁
module CN₁ = R₁.Check NDm.NDAnswer
module CM₁ = R₁.Check MB.MaybeAnswer

-- `Ambiguous.ambig` needs only a covariant answer; `Dec` has none.
ndRes₁ : CN₁.Checker R₁.ResSet
ndRes₁ = CN₁.resolver (CN₁.Ambiguous.ambig NDm.NDCov)

mayRes₁ : CM₁.Checker R₁.ResSet
mayRes₁ = CM₁.resolver (CM₁.Ambiguous.ambig MB.MaybeCov)

count₁ : Cls → Typ → ℕ
count₁ C t = length (NDm.ndToList t (ndRes₁ C t tt))

resolve₁ : Cls → Typ → Maybe Dict
resolve₁ C t = Sum.rec (λ d → just (R₁.toDict C t d)) (λ _ → nothing)
  (mayRes₁ C t tt)

nd-overlap : count₁ eqC (lst ι) ≡ 2
nd-overlap = refl

nd-overlap-nested : count₁ eqC (lst (lst ι)) ≡ 4
nd-overlap-nested = refl

-- Unambiguous counts are 1, so the 2 above is overlap, not enumeration.
nd-overlap-base : count₁ eqC ι ≡ 1
nd-overlap-base = refl

nd-overlap-ord : count₁ ordC (lst (lst ι)) ≡ 1
nd-overlap-ord = refl

module CN₀' = R₀.Check NDm.NDAnswer

countAmb₀ : Cls → Typ → ℕ
countAmb₀ C t = length (NDm.ndToList t
  (CN₀'.resolver (CN₀'.Ambiguous.ambig NDm.NDCov) C t tt))

nd-amb-agrees : countAmb₀ eqC (lst (lst ι)) ≡ 1
nd-amb-agrees = refl

-- `Maybe` silently takes the first instance that fires.
may-overlap : resolve₁ eqC (lst ι) ≡ just (dict 1 (dict 0 [] ∷ []))
may-overlap = refl
