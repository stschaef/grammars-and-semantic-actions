{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The identification the `tally` tests are pointing at.

   `Cover Y Λ` has two fields, and a clause list has two properties:

     total     every value matches some clause -- exhaustiveness
     disjoint  no value matches two            -- irredundancy

   So "this clause list is exhaustive and irredundant" is not a pair of
   ad hoc lemmas; it is `Cover (Fin n) (λ i → Match (clause i))`, the same
   record `Combinator/Core`'s `look` consumes.  `tally cs v ≡ 1` for every
   `v` is the computational shadow of it.

   The concrete cover below is the *node cover relabelled*.  `full` has one
   clause per head constructor, so `nodeOf` sends a derivation to the cell
   of `Guard`'s `nodeCover` it lives in, and `disjoint` is then no-confusion
   for `Val` transported along an injection `Fin 3 ↪ VOp` -- nothing about
   patterns is used.  That is the honest content of the identification: a
   complete irredundant clause list at depth one *is* a cover by head, and
   deeper clause lists are covers of covers.

   What is not proved here: nothing general.  This is one list, and there is
   no theorem "`Cover` implies `tally ≡ 1`" -- that would have to relate the
   `ND` enumeration to the cover's index type, and the enumeration is a list
   with an order while the cover is not. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Match.Exhaustive where

import Cubical.Data.Empty as Empty
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.FinData.Properties using (discreteFin)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sigma using (Σ-syntax ; ΣPathP ; _,_ ; fst ; snd)
import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit using (tt)
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no)
import Cubical.Data.Equality as Eq

open import Theory.Instances.Match.Judgment

-- One clause per head constructor.
full : List Pat
full = ptrue ∷ pfalse ∷ ppair pwild pwild ∷ []

Clause : Fin 3 → Pat
Clause zero = ptrue
Clause (suc zero) = pfalse
Clause (suc (suc zero)) = ppair pwild pwild

-- ...which is what makes the clause index a retract of the operation.
clauseHead : Fin 3 → VOp
clauseHead zero = vtrueOp
clauseHead (suc zero) = vfalseOp
clauseHead (suc (suc zero)) = vpairOp

headClause : VOp → Fin 3
headClause vtrueOp = zero
headClause vfalseOp = suc zero
headClause vpairOp = suc (suc zero)

private
  headRet : (i : Fin 3) → headClause (clauseHead i) ≡ i
  headRet zero = refl
  headRet (suc zero) = refl
  headRet (suc (suc zero)) = refl

  headInj : (i j : Fin 3) → clauseHead i Eq.≡ clauseHead j → i Eq.≡ j
  headInj i j e = Eq.pathToEq
    (sym (headRet i) ∙ cong headClause (Eq.eqToPath e) ∙ headRet j)

  -- The off-diagonal cases are `Judgment`'s `clash` lemmas: a derivation
  -- carries an equation now, so a wrong head is refuted rather than absurd.
  nodeOf : (i : Fin 3) → Match (Clause i) ⊢ NodeAt (clauseHead i)
  nodeOf zero vtrue _ = (λ ()) , Eq.refl
  nodeOf zero vfalse d = Empty.rec (clashTrue vfalse d)
  nodeOf zero (vpair v w) d = Empty.rec (clashTrue (vpair v w) d)
  nodeOf (suc zero) vtrue d = Empty.rec (clashFalse vtrue d)
  nodeOf (suc zero) vfalse _ = (λ ()) , Eq.refl
  nodeOf (suc zero) (vpair v w) d = Empty.rec (clashFalse (vpair v w) d)
  nodeOf (suc (suc zero)) vtrue d = Empty.rec (clashPair pwild pwild vtrue d)
  nodeOf (suc (suc zero)) vfalse d = Empty.rec (clashPair pwild pwild vfalse d)
  nodeOf (suc (suc zero)) (vpair v w) _ = pairArgs v w , Eq.refl

-- Exhaustive and irredundant, as one record.
clauseCover : Cover (Fin 3) (λ i → Match (Clause i))
clauseCover .total vtrue _ = zero , (tt , refl)
clauseCover .total vfalse _ = suc zero , (tt , refl)
clauseCover .total (vpair v w) _ = suc (suc zero) , ((v , w) , refl)
clauseCover .disjoint i j ne v (d , e) =
  nodeCover .disjoint (clauseHead i) (clauseHead j)
    (λ q → ne (headInj i j q)) v (nodeOf i v d , nodeOf j v e)

-- The clause list `full` and the cover's index are the same thing, so what
-- the cover says transfers to the grammar the matcher actually runs on.
toCells : (v : Val) → Any full v → Σ[ i ∈ Fin 3 ] Match (Clause i) v
toCells v (Sum.inl d) = zero , d
toCells v (Sum.inr (Sum.inl d)) = suc zero , d
toCells v (Sum.inr (Sum.inr (Sum.inl d))) = suc (suc zero) , d
toCells v (Sum.inr (Sum.inr (Sum.inr ())))

fromCells : (v : Val) → Σ[ i ∈ Fin 3 ] Match (Clause i) v → Any full v
fromCells v (zero , d) = Sum.inl d
fromCells v (suc zero , d) = Sum.inr (Sum.inl d)
fromCells v (suc (suc zero) , d) = Sum.inr (Sum.inr (Sum.inl d))

private
  cellRet : (v : Val) (d : Any full v) → fromCells v (toCells v d) ≡ d
  cellRet v (Sum.inl d) = refl
  cellRet v (Sum.inr (Sum.inl d)) = refl
  cellRet v (Sum.inr (Sum.inr (Sum.inl d))) = refl
  cellRet v (Sum.inr (Sum.inr (Sum.inr ())))

exhaustive : (v : Val) → Any full v
exhaustive v = fromCells v (clauseCover .total v tt)

-- Irredundancy, read on the list: two derivations at one value come from
-- one clause, and a clause's derivation is unique.
sameClause : (v : Val) (d e : Any full v)
  → toCells v d .fst ≡ toCells v e .fst
sameClause v d e = decide (discreteFin i j)
  where
  i j : Fin 3
  i = toCells v d .fst
  j = toCells v e .fst

  decide : Dec (i ≡ j) → i ≡ j
  decide (yes p) = p
  decide (no ¬p) = Empty.rec*
    (clauseCover .disjoint i j (λ q → ¬p (Eq.eqToPath q)) v
      (toCells v d .snd , toCells v e .snd))

irredundant : (v : Val) → isProp (Any full v)
irredundant v d e =
  sym (cellRet v d) ∙ cong (fromCells v) cells≡ ∙ cellRet v e
  where
  same : toCells v d .fst ≡ toCells v e .fst
  same = sameClause v d e

  cells≡ : toCells v d ≡ toCells v e
  cells≡ = ΣPathP (same ,
    isProp→PathP (λ k → isPropMatch (Clause (same k)) v) _ _)

-- ...so a complete clause list has exactly one derivation everywhere, which
-- is what `tally full v ≡ 1` observes one value at a time.
covers : (v : Val) → isContr (Any full v)
covers v = exhaustive v , irredundant v (exhaustive v)
