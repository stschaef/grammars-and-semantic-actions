{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isOfHLevelRetract)
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Lambda.Signature where

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.FinData.Properties using (isSetFin)
open import Cubical.Data.Empty using (⊥)

data LSort : Type ℓ-zero where
  nm tm : LSort

data LOp : Type ℓ-zero where
  varOp appOp lamOp : LOp

LAr : LOp → ℕ
LAr varOp = 1
LAr appOp = 2
LAr lamOp = 2

LSortOf : (o : LOp) → Fin (LAr o) → LSort
LSortOf varOp _ = nm
LSortOf appOp _ = tm
LSortOf lamOp zero = nm
LSortOf lamOp (suc zero) = tm

λSig : SortedSig LSort ℓ-zero
λSig .ops = LOp
λSig .arity = LAr
λSig .sortOf = LSortOf
λSig .resultSort _ = tm

λEqns : SortedEqns λSig ℓ-zero
λEqns .eqns = ⊥
λEqns .eqnSort ()
λEqns .varCount ()
λEqns .varSort ()
λEqns .lhs ()
λEqns .rhs ()

private
  toFin : LOp → Fin 3
  toFin varOp = zero
  toFin appOp = suc zero
  toFin lamOp = suc (suc zero)

  fromFin : Fin 3 → LOp
  fromFin zero = varOp
  fromFin (suc zero) = appOp
  fromFin (suc (suc zero)) = lamOp

  finRet : (o : LOp) → fromFin (toFin o) ≡ o
  finRet varOp = refl
  finRet appOp = refl
  finRet lamOp = refl

isSetLOp : isSet LOp
isSetLOp = isOfHLevelRetract 2 toFin fromFin finRet isSetFin
