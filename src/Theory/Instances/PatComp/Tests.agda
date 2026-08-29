{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- One compiler, three answers -- and here, unlike `Match`, the three had
   better agree.

   `Match`'s `tally` was a static analysis: two meant the clause list was
   redundant at that value, zero meant the value was a counterexample to
   exhaustiveness, and the number was the point.  Compilation is not like
   that.  `Ok` determines the tree from the matrix, so `Comp n P` is a
   proposition and `tally` is one everywhere; a two would say the algorithm
   had a choice to make, and it does not.  Exhaustiveness and redundancy
   have moved OUT of the answer and INTO the output -- they are `noFail`
   and `labels`, syntactic tests on the tree the `Dec` answer returned.

   The tests are `refl`, so the typechecker runs the compiler, the guarded
   fixpoint and all three answers on concrete matrices. -}
open import Cubical.Foundations.Prelude
module Theory.Instances.PatComp.Tests where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Properties using (znots ; injSuc)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
import Cubical.Data.Sum as Sum

open import Theory.Instances.PatComp.Check

-- A partial matrix: `true` and nothing else.
partial : Mat 1
partial = (ptrue ◂ ⇒ 0) ∷ []

-- ...the same with a catch-all after it, and then a row nothing can reach.
shadowed : Mat 1
shadowed = (ptrue ◂ ⇒ 0) ∷ (pwild ◂ ⇒ 1) ∷ (ptrue ◂ ⇒ 2) ∷ []

-- ...and one clause per head, which is `Match/Exhaustive`'s `full`.
full1 : Mat 1
full1 = (ptrue ◂ ⇒ 0) ∷ (pfalse ◂ ⇒ 1) ∷ (ppair pwild pwild ◂ ⇒ 2) ∷ []

-- Two columns, and no column is decided by the first: row 0 constrains
-- column one, row 1 constrains column two, row 2 constrains both.  This is
-- the matrix whose tree has a shape.
wide : Mat 2
wide = (ptrue ◂ pwild ◂ ⇒ 0)
     ∷ (pwild ◂ pfalse ◂ ⇒ 1)
     ∷ (ppair pwild pwild ◂ ptrue ◂ ⇒ 2)
     ∷ []

-- ...and a column of nothing but wildcards, which is the step the
-- constructor count does not pay for and the width does.
blind : Mat 2
blind = (pwild ◂ ptrue ◂ ⇒ 0) ∷ (pwild ◂ pfalse ◂ ⇒ 1) ∷ []


-- `Dec`: the tree, and the algorithm always succeeds.
dec-partial : compile 1 partial ≡ just (tswitch (tleaf 0) tskip tskip tfail)
dec-partial = refl

dec-shadowed : compile 1 shadowed ≡ just (tswitch (tleaf 0) tskip tskip (tleaf 1))
dec-shadowed = refl

-- A complete head column: no default at all, and `tskip` nowhere.
dec-full1 : compile 1 full1
          ≡ just (tswitch (tleaf 0) (tleaf 1)
              (tswitch tskip tskip tskip (tswitch tskip tskip tskip (tleaf 2)))
              tskip)
dec-full1 = refl

dec-empty : compile 1 [] ≡ just tfail
dec-empty = refl

-- The interesting one.  Reading it: at a `true` first component switch on
-- the second; at a `false` first component nothing in column one applies,
-- so fall to the default; at a pair, unpack it, find that neither of the
-- two surviving rows constrains either new column, drop them both, and
-- only then switch on the original second column.
dec-wide : compile 2 wide
  ≡ just (tswitch
            (tswitch tskip (tleaf 0) tskip (tleaf 0))
            tskip
            (tswitch tskip tskip tskip
              (tswitch tskip tskip tskip
                (tswitch (tleaf 2) (tleaf 1) tskip tfail)))
            (tswitch tskip (tleaf 1) tskip tfail))
dec-wide = refl

-- The head column is all wildcards, so every branch is absent and the
-- switch is a pure column drop -- the step the lexicographic order's
-- second component pays for.
dec-blind : compile 2 blind
  ≡ just (tswitch tskip tskip tskip
           (tswitch (tleaf 0) (tleaf 1) tskip tfail))
dec-blind = refl


-- `Maybe` agrees with `Dec`, because there is nothing to commit to.
may-wide : compileFirst 2 wide ≡ compile 2 wide
may-wide = refl

may-partial : compileFirst 1 partial ≡ compile 1 partial
may-partial = refl


-- `ND` counts one, everywhere.  That is the claim that compilation is
-- deterministic, and it is the only reading under which the three answers
-- are allowed to agree.
nd-partial : tally 1 partial ≡ 1
nd-partial = refl

nd-wide : tally 2 wide ≡ 1
nd-wide = refl

nd-empty : tally 1 [] ≡ 1
nd-empty = refl

nd-blind : tally 2 blind ≡ 1
nd-blind = refl


-- EXHAUSTIVENESS, read off the tree.  `noFail` is `false` exactly where
-- `Match`'s `tally` would have returned zero at some value.
exh-partial : noFail (tswitch (tleaf 0) tskip tskip tfail) ≡ false
exh-partial = refl

exh-shadowed : noFail (tswitch (tleaf 0) tskip tskip (tleaf 1)) ≡ true
exh-shadowed = refl

exh-full1 : noFail (tswitch (tleaf 0) (tleaf 1)
              (tswitch tskip tskip tskip (tswitch tskip tskip tskip (tleaf 2)))
              tskip) ≡ true
exh-full1 = refl

-- ...and the counterexample the failing tree is pointing at.
exh-witness : matrixRun partial (vfalse ▸ ⟨⟩) ≡ nothing
exh-witness = refl

exh-wide-witness : matrixRun wide (vfalse ▸ vtrue ▸ ⟨⟩) ≡ nothing
exh-wide-witness = refl


-- REDUNDANCY, read off the tree.  Row two of `shadowed` labels no leaf, so
-- `redundant` says no value selects it -- and the enumeration is short
-- enough to write down.
red-shadowed : labels (tswitch (tleaf 0) tskip tskip (tleaf 1))
             ≡ 0 ∷ 1 ∷ []
red-shadowed = refl

red-dead : Mem 2 (0 ∷ 1 ∷ []) → Empty.⊥
red-dead (Sum.inl e) = znots e
red-dead (Sum.inr (Sum.inl e)) = znots (injSuc e)
red-dead (Sum.inr (Sum.inr ()))

-- ...which is the hypothesis of `redundant`, so row two of `shadowed` is
-- unreachable at every value at once, and not one value at a time.
red-unreachable : (vs : Vals 1) → matrixRun shadowed vs ≡ just 2 → Empty.⊥
red-unreachable = redundant 1 (tswitch (tleaf 0) tskip tskip (tleaf 1))
  shadowed (tt , (tt , refl) , tt , tt , tt , refl) 2 red-dead


-- The tree runs the matrix, one value at a time -- the computational
-- shadow of `sound`.
run-wide-0 : runTree (tswitch
            (tswitch tskip (tleaf 0) tskip (tleaf 0))
            tskip
            (tswitch tskip tskip tskip
              (tswitch tskip tskip tskip
                (tswitch (tleaf 2) (tleaf 1) tskip tfail)))
            (tswitch tskip (tleaf 1) tskip tfail))
            (vtrue ▸ vtrue ▸ ⟨⟩)
          ≡ matrixRun wide (vtrue ▸ vtrue ▸ ⟨⟩)
run-wide-0 = refl

run-blind : runTree (tswitch tskip tskip tskip
              (tswitch (tleaf 0) (tleaf 1) tskip tfail))
              (vpair vtrue vfalse ▸ vfalse ▸ ⟨⟩)
          ≡ matrixRun blind (vpair vtrue vfalse ▸ vfalse ▸ ⟨⟩)
run-blind = refl
