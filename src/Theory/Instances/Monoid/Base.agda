open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Base where

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.FinData.More public
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty using (⊥)

Sorts : Type ℓ-zero
Sorts = Unit

data MonOp : Type ℓ-zero where
  ε· : MonOp
  _⊙_ : MonOp

MonSig : SortedSig Sorts ℓ-zero
MonSig .ops = MonOp
MonSig .arity ε· = 0
MonSig .arity _⊙_ = 2
MonSig .sortOf _ _ = tt
MonSig .resultSort _ = tt

private variable ℓv : Level

module _ {ℓV} {V : Type ℓV} {vs : V → Sorts} where
  infixr 20 _·_
  _·_ : Tm MonSig V vs tt → Tm MonSig V vs tt → Tm MonSig V vs tt
  t · u = node _⊙_ (two t u)

  ε : Tm MonSig V vs tt
  ε = node ε· λ ()

data MonEqn : Type ℓ-zero where
  assoc unitL unitR : MonEqn

MonEqns : SortedEqns MonSig ℓ-zero
MonEqns .eqns = MonEqn
MonEqns .eqnSort _ = tt
MonEqns .varCount assoc = 3
MonEqns .varCount unitL = 1
MonEqns .varCount unitR = 1
MonEqns .varSort _ _ = tt
MonEqns .lhs assoc =
  (var zero · var (suc zero)) · var (suc (suc zero))
MonEqns .rhs assoc =
  var zero · (var (suc zero) · var (suc (suc zero)))
MonEqns .lhs unitL = ε · var zero
MonEqns .rhs unitL = var zero
MonEqns .lhs unitR = var zero · ε
MonEqns .rhs unitR = var zero
