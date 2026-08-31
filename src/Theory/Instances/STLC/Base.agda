{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Raw syntax for simply typed lambda calculus.  Types and terms are both
   syntax in the free model; typing is added in `WellTyped`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isOfHLevelRetract)
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.STLC.Base
  (BaseType Name : Type ℓ-zero)
  (isSetBaseType : isSet BaseType) (isSetName : isSet Name) where

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.FinData.Properties using (isSetFin)
open import Cubical.Data.FinData.More public
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr ; isSet⊎)
open import Cubical.Data.Unit using (Unit ; tt ; Unit* ; tt*)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

data STLCSort : Type ℓ-zero where
  nm ty tm : STLCSort

data STLCOp : Type ℓ-zero where
  baseOp : BaseType → STLCOp
  arrOp varOp appOp lamOp : STLCOp

Ar : STLCOp → ℕ
Ar (baseOp _) = 0
Ar arrOp      = 2
Ar varOp      = 1
Ar appOp      = 2
Ar lamOp      = 3

SortOf : (o : STLCOp) → Fin (Ar o) → STLCSort
SortOf (baseOp b) ()
SortOf arrOp zero = ty
SortOf arrOp (suc zero) = ty
SortOf varOp _ = nm
SortOf appOp _ = tm
SortOf lamOp zero = nm
SortOf lamOp (suc zero) = ty
SortOf lamOp (suc (suc zero)) = tm

Result : STLCOp → STLCSort
Result (baseOp _) = ty
Result arrOp = ty
Result varOp = tm
Result appOp = tm
Result lamOp = tm

STLCSig : SortedSig STLCSort ℓ-zero
STLCSig .ops = STLCOp
STLCSig .arity = Ar
STLCSig .sortOf = SortOf
STLCSig .resultSort = Result

STLCEqns : SortedEqns STLCSig ℓ-zero
STLCEqns .eqns = ⊥
STLCEqns .eqnSort ()
STLCEqns .varCount ()
STLCEqns .varSort ()
STLCEqns .lhs ()
STLCEqns .rhs ()


-- h-level of the sorts and operations, for the term presentation below.
private
  sortToFin : STLCSort → Fin 3
  sortToFin nm = zero
  sortToFin ty = suc zero
  sortToFin tm = suc (suc zero)

  sortFromFin : Fin 3 → STLCSort
  sortFromFin zero = nm
  sortFromFin (suc zero) = ty
  sortFromFin (suc (suc zero)) = tm

  sortRet : (s : STLCSort) → sortFromFin (sortToFin s) ≡ s
  sortRet nm = refl
  sortRet ty = refl
  sortRet tm = refl

  opToRep : STLCOp → BaseType ⊎ Fin 4
  opToRep (baseOp b) = inl b
  opToRep arrOp = inr zero
  opToRep varOp = inr (suc zero)
  opToRep appOp = inr (suc (suc zero))
  opToRep lamOp = inr (suc (suc (suc zero)))

  opFromRep : BaseType ⊎ Fin 4 → STLCOp
  opFromRep (inl b) = baseOp b
  opFromRep (inr zero) = arrOp
  opFromRep (inr (suc zero)) = varOp
  opFromRep (inr (suc (suc zero))) = appOp
  opFromRep (inr (suc (suc (suc zero)))) = lamOp

  opRet : (o : STLCOp) → opFromRep (opToRep o) ≡ o
  opRet (baseOp b) = refl
  opRet arrOp = refl
  opRet varOp = refl
  opRet appOp = refl
  opRet lamOp = refl

isSetSTLCSort : isSet STLCSort
isSetSTLCSort = isOfHLevelRetract 2 sortToFin sortFromFin sortRet isSetFin

isSetSTLCOp : isSet STLCOp
isSetSTLCOp = isOfHLevelRetract 2 opToRep opFromRep opRet
  (isSet⊎ isSetBaseType isSetFin)

open import Theory.Free.Term STLCEqns Name (λ _ → nm)
  (λ ()) isSetSTLCSort isSetName isSetSTLCOp public
  using (termPresentation ; genT ; opT ; TermView ; isGen ; isOp ; termView
        ; elimTerm)
open import Theory.Base STLCEqns Name (λ _ → nm) termPresentation public
open import Theory.Type.Lift.Base STLCEqns Name (λ _ → nm) termPresentation public
open import Theory.Type.Sum.Base STLCEqns Name (λ _ → nm) termPresentation public
open import Theory.Type.Operation.Base STLCEqns Name (λ _ → nm) termPresentation public
open import Theory.Type.Inductive.Base STLCEqns Name (λ _ → nm) termPresentation public

Raw : Type ℓM
Raw = ↓M tm

Ty : Type ℓM
Ty = ↓M ty

Nm : Type ℓM
Nm = ↓M nm

private variable ℓA ℓB ℓC : Level

base : BaseType → Ty
base b = op (baseOp b) λ ()

_⇒_ : Ty → Ty → Ty
A ⇒ B = op arrOp (two A B)
infixr 25 _⇒_

mkVar : Nm → Raw
mkVar x = op varOp λ _ → x

mkApp : Raw → Raw → Raw
mkApp f a = op appOp (two f a)

mkLam : Nm → Ty → Raw → Raw
mkLam x A t = op lamOp (three x A t)

BaseTy : (b : BaseType) → TheoryTy ℓM ty
BaseTy b = ⊗[ baseOp b ][ (λ ()) ] tt*

ArrowTy : TheoryTy ℓA ty → TheoryTy ℓB ty → TheoryTy _ ty
ArrowTy {ℓA = ℓA} {ℓB = ℓB} A B =
  ⊗[ arrOp ][ two ℓA ℓB ] (A , B , tt*)

VarTy : TheoryTy ℓA nm → TheoryTy _ tm
VarTy {ℓA = ℓA} P = ⊗[ varOp ][ (λ _ → ℓA) ] (P , tt*)

AppTy : TheoryTy ℓA tm → TheoryTy ℓB tm → TheoryTy _ tm
AppTy {ℓA = ℓA} {ℓB = ℓB} A B =
  ⊗[ appOp ][ two ℓA ℓB ] (A , B , tt*)

LamTy : TheoryTy ℓA nm → TheoryTy ℓB ty → TheoryTy ℓC tm → TheoryTy _ tm
LamTy {ℓA = ℓA} {ℓB = ℓB} {ℓC = ℓC} P A B =
  ⊗[ lamOp ][ three ℓA ℓB ℓC ] (P , A , B , tt*)
