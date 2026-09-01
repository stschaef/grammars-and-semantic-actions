{-# OPTIONS --no-lossy-unification -WnoUnsupportedIndexedMatch #-}
{- MUST NOT have `--lossy-unification`: `may-wide`/`may-partial` compare the
   same term at `𝒯 := DecAnswer` vs `𝒯 := MaybeAnswer`, so the first-order
   approximation retries `DecAnswer =?= MaybeAnswer` at every subtree; cost is
   exponential in tree depth.  Measured (vs 2.2s / 0.4GB import baseline):
     w = 1     3.6s    0.6 GB
     w = 2    10.0s    1.4 GB
     w = 3    34.6s    4.4 GB
     w = 4    stopped at 16 GB, still running
     may-wide stopped at 13 GB, still running
   Flag off: whole file 11s / 2.3 GB. -}
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

partial : Mat 1
partial = (ptrue ◂ ⇒ 0) ∷ []

shadowed : Mat 1
shadowed = (ptrue ◂ ⇒ 0) ∷ (pwild ◂ ⇒ 1) ∷ (ptrue ◂ ⇒ 2) ∷ []

full1 : Mat 1
full1 = (ptrue ◂ ⇒ 0) ∷ (pfalse ◂ ⇒ 1) ∷ (ppair pwild pwild ◂ ⇒ 2) ∷ []

wide : Mat 2
wide = (ptrue ◂ pwild ◂ ⇒ 0)
     ∷ (pwild ◂ pfalse ◂ ⇒ 1)
     ∷ (ppair pwild pwild ◂ ptrue ◂ ⇒ 2)
     ∷ []

blind : Mat 2
blind = (pwild ◂ ptrue ◂ ⇒ 0) ∷ (pwild ◂ pfalse ◂ ⇒ 1) ∷ []


dec-partial : compile 1 partial ≡ just (tswitch (tleaf 0) tskip tskip tfail)
dec-partial = refl

dec-shadowed : compile 1 shadowed ≡ just (tswitch (tleaf 0) tskip tskip (tleaf 1))
dec-shadowed = refl

dec-full1 : compile 1 full1
          ≡ just (tswitch (tleaf 0) (tleaf 1)
              (tswitch tskip tskip tskip (tswitch tskip tskip tskip (tleaf 2)))
              tskip)
dec-full1 = refl

dec-empty : compile 1 [] ≡ just tfail
dec-empty = refl

dec-wide : compile 2 wide
  ≡ just (tswitch
            (tswitch tskip (tleaf 0) tskip (tleaf 0))
            tskip
            (tswitch tskip tskip tskip
              (tswitch tskip tskip tskip
                (tswitch (tleaf 2) (tleaf 1) tskip tfail)))
            (tswitch tskip (tleaf 1) tskip tfail))
dec-wide = refl

dec-blind : compile 2 blind
  ≡ just (tswitch tskip tskip tskip
           (tswitch (tleaf 0) (tleaf 1) tskip tfail))
dec-blind = refl


may-wide : compileFirst 2 wide ≡ compile 2 wide
may-wide = refl

may-partial : compileFirst 1 partial ≡ compile 1 partial
may-partial = refl


nd-partial : tally 1 partial ≡ 1
nd-partial = refl

nd-wide : tally 2 wide ≡ 1
nd-wide = refl

nd-empty : tally 1 [] ≡ 1
nd-empty = refl

nd-blind : tally 2 blind ≡ 1
nd-blind = refl


exh-partial : noFail (tswitch (tleaf 0) tskip tskip tfail) ≡ false
exh-partial = refl

exh-shadowed : noFail (tswitch (tleaf 0) tskip tskip (tleaf 1)) ≡ true
exh-shadowed = refl

exh-full1 : noFail (tswitch (tleaf 0) (tleaf 1)
              (tswitch tskip tskip tskip (tswitch tskip tskip tskip (tleaf 2)))
              tskip) ≡ true
exh-full1 = refl

exh-witness : matrixRun partial (vfalse ▸ ⟨⟩) ≡ nothing
exh-witness = refl

exh-wide-witness : matrixRun wide (vfalse ▸ vtrue ▸ ⟨⟩) ≡ nothing
exh-wide-witness = refl


red-shadowed : labels (tswitch (tleaf 0) tskip tskip (tleaf 1))
             ≡ 0 ∷ 1 ∷ []
red-shadowed = refl

red-dead : Mem 2 (0 ∷ 1 ∷ []) → Empty.⊥
red-dead (Sum.inl e) = znots e
red-dead (Sum.inr (Sum.inl e)) = znots (injSuc e)
red-dead (Sum.inr (Sum.inr ()))

red-unreachable : (vs : Vals 1) → matrixRun shadowed vs ≡ just 2 → Empty.⊥
red-unreachable = redundant 1 (tswitch (tleaf 0) tskip tskip (tleaf 1))
  shadowed (tt , (tt , refl) , tt , tt , tt , refl) 2 red-dead


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
