{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `Scope`, at the graded answer: linearity as a typing fact.

   `CostTests` computes six rows of a doubling table and then explains why
   the rows are where it stops -- the universal recurrences are true and
   not `refl`, because `löb-unfold` is propositional.  `linear` below is
   the statement those rows were evidence for, quantified over EVERY
   context and EVERY term, and it is four lines, because the bound is
   carried inside the answer instead of being asserted about the checker.
   Nothing here unfolds the fixpoint.

   THE MEASURE, and why it is `2 · tmSize` rather than `tmSize`.  The
   checker spends one step per node plus one per side condition, and the
   lambda grammar has a side condition at two of its three operations --
   `decInCtx` at `varOp`, the vacuous `dec⊤` at `lamOp`'s binder slot.  So
   `tvar x` costs 2 while `tmSize (tvar x)` is 1, and `Linear`'s `sizeNode`
   -- which charges the node one unit of `size` and no more -- is unsatisfiable
   at `tmSize` for any `k`: the constant cannot be paid by the multiplier,
   because `sizeNode` does not mention it.  Folding it into the measure is
   the same thing and is what `Bounded.absorb-*` says is always available:
   `tmSize2` is `2 · tmSize` (proved, not assumed) and `k = 1`.

   That `tmSize2` is linear in the term is the CLIENT's obligation, and
   `tmSize2≡` is where it is met.  `sizeNode` bounds `size` from below, so
   the interface alone would be satisfied by an exponential measure; what
   makes `linear` a linearity theorem is that the measure is exhibited as
   twice the syntactic size. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Lambda.Bounded where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Nat
  using (ℕ ; zero ; suc ; _+_ ; _·_ ; isSetℕ ; discreteℕ
        ; +-zero ; ·-suc ; ·-identityˡ ; ·-distribˡ)
open import Cubical.Data.Nat.Order using (_≤_ ; ≤-refl ; zero-≤ ; suc-≤-suc)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum

open import Theory.Instances.Lambda.Scope ℕ isSetℕ discreteℕ

import Theory.Combinator.Answer.Decidable
  λEqns ℕ (λ _ → nm) termPresentation as D
open import Theory.Combinator.Linear λEqns ℕ (λ _ → nm) termPresentation

-- Two units per node, which is what the checker actually spends: one for
-- the node rule and one for the side condition riding on it.  Written as
-- its own recursion so that `sizeNode` is discharged by `+-zero` alone,
-- and related to `tmSize` immediately afterwards so that nothing rests on
-- the reader believing the name.
tmSize2 : RawTm → ℕ
tmSize2 (tvar _) = 2
tmSize2 (tapp t u) = suc (suc (tmSize2 t + tmSize2 u))
tmSize2 (tlam _ t) = suc (suc (tmSize2 t))

tmSize2≡ : (t : RawTm) → tmSize2 t ≡ 2 · tmSize t
tmSize2≡ (tvar _) = refl
tmSize2≡ (tapp t u) =
  cong₂ (λ a b → 2 + (a + b)) (tmSize2≡ t) (tmSize2≡ u)
  ∙ cong (2 +_) (·-distribˡ 2 (tmSize t) (tmSize u))
  ∙ sym (·-suc 2 (tmSize t + tmSize u))
tmSize2≡ (tlam _ t) =
  cong (2 +_) (tmSize2≡ t) ∙ sym (·-suc 2 (tmSize t))

-- The measure at both sorts.  A name is a leaf that a side condition is
-- asked about, so it is worth exactly the one step that asking costs.
lsize : {s : LSort} → ↓M s → ℕ
lsize {nm} _ = 1
lsize {tm} t = tmSize2 t

lsizePos : {s : LSort} (m : ↓M s) → 1 ≤ lsize m
lsizePos {nm} _ = ≤-refl
lsizePos {tm} (tvar _) = suc-≤-suc zero-≤
lsizePos {tm} (tapp t u) = suc-≤-suc zero-≤
lsizePos {tm} (tlam _ t) = suc-≤-suc zero-≤

-- Superadditivity, one clause per operation.  `varOp` is tight -- a
-- variable is exactly a node and a lookup -- `lamOp` is tight, and `appOp`
-- has one unit of slack, which is the `+ 1` visible in `app2` below.
lsizeNode : (o : LOp) (ms : interpIn o ↓M)
  → suc (sumFin (λ a → lsize (ms a))) ≤ lsize (op o ms)
lsizeNode varOp ms = ≤-refl
lsizeNode appOp ms =
  1 , cong (λ z → 2 + (tmSize2 (ms theFun) + z))
           (+-zero (tmSize2 (ms theArg)))
lsizeNode lamOp ms =
  0 , cong (2 +_) (+-zero (tmSize2 (ms theBody)))

-- `k = 1`: the per-node constant lives in the measure, per `absorb-*`.
module B = Bounded D.DecAnswer 1 lsize ≤-refl lsizePos lsizeNode
module CB = CheckL B.bounded

-- the checker, unchanged, now returning its own certificate
boundedScope : (Γ : Ctx) → ⊤Ty ⊢ ty (B.BAns (ScopeSet Γ))
boundedScope = CB.scoped

steps : Ctx → RawTm → ℕ
steps Γ t = boundedScope Γ t tt .fst

decides : Ctx → RawTm → Bool
decides Γ t = Sum.rec (λ _ → true) (λ _ → false) (boundedScope Γ t tt .snd .snd)

-- THE THEOREM.  Every context, every term, no `refl`, no `löb-unfold`:
-- the certificate rode along inside the answer, so `fix` transported it.
linear : (Γ : Ctx) (t : RawTm) → steps Γ t ≤ 2 · tmSize t
linear Γ t = subst (steps Γ t ≤_) bnd (boundedScope Γ t tt .snd .fst)
  where
  bnd : 1 · tmSize2 t ≡ 2 · tmSize t
  bnd = ·-identityˡ (tmSize2 t) ∙ tmSize2≡ t

-- ...and the count is the one `CostTests` tabulated, so the certificate is
-- about the run that table timed.
nest : ℕ → RawTm
nest zero = tvar 0
nest (suc n) = tlam 0 (nest n)

row0 : steps [] (nest 0) ≡ 2
row0 = refl

row2 : steps [] (nest 2) ≡ 6
row2 = refl

row8 : steps [] (nest 8) ≡ 18
row8 = refl

row16 : steps [] (nest 16) ≡ 34
row16 = refl

app2 : steps [] (tapp (nest 1) (nest 1)) ≡ 9
app2 = refl

-- `nest 16` saturates the bound and `tapp` does not, which is `lsizeNode`'s
-- one unit of slack showing up in the arithmetic rather than in prose.
tight16 : 2 · tmSize (nest 16) ≡ 34
tight16 = refl

slack : 2 · tmSize (tapp (nest 1) (nest 1)) ≡ 10
slack = refl

-- ...and the answers are `ScopeTests`' answers, so the port is faithful.
idT : RawTm
idT = tlam 0 (tvar 0)

capture : RawTm
capture = tlam 0 (tapp (tvar 0) (tvar 1))

dec-id : decides [] idT ≡ true
dec-id = refl

dec-open : decides [] (tvar 0) ≡ false
dec-open = refl

dec-capture : decides [] capture ≡ false
dec-capture = refl

dec-capture-in-ctx : decides (1 ∷ []) capture ≡ true
dec-capture-in-ctx = refl

dec-shadow : decides [] (tlam 0 (tlam 0 (tvar 0))) ≡ true
dec-shadow = refl

-- THE FIELD THAT IS NOT HERE.  `LinearCombinators` has no `_<|>_`, and
-- this is why: at `tvar 0` the budget is 2, so an alternation that charged
-- what `Cost` charges would have to certify `4 ≤ 2`.  `Linear` derives the
-- `⊥`; here it is at this instance, with the numbers filled in.
noAlternation :
  (alt : ty (B.BAns B.⊤Set) & ty (B.BAns B.⊤Set)
       ⊢ ty (B.BAns (B.⊤Set ⊕Set B.⊤Set)))
  → alt (tvar 0) (B.both (tvar 0)) .fst ≡ 4
  → Empty.⊥
noAlternation = B.⊕&-impossible (tvar 0)

noConjunction :
  (cnj : ty (B.BAns B.⊤Set) & ty (B.BAns B.⊤Set)
       ⊢ ty (B.BAns (B.⊤Set &Set B.⊤Set)))
  → cnj (tvar 0) (B.both (tvar 0)) .fst ≡ 4
  → Empty.⊥
noConjunction = B.&&-impossible (tvar 0)

-- ONE COST MODEL, NOT TWO.  `Linear` re-declares `Cost`'s `sumFin`,
-- because that one is private; these are the check that the copy is
-- faithful, and that `linear`'s certificate therefore bounds the count
-- `CostTests` tabulates rather than a second count that resembles it.
import Theory.Combinator.Cost λEqns ℕ (λ _ → nm) termPresentation as Cst

module CG = Cst.Costed D.DecAnswer
module CC = Check CG.costed

sameCost-nest : steps [] (nest 4) ≡ CG.stepsOf (CC.scoped []) (nest 4)
sameCost-nest = refl

sameCost-app : steps [] (tapp (nest 1) (nest 1))
             ≡ CG.stepsOf (CC.scoped []) (tapp (nest 1) (nest 1))
sameCost-app = refl
