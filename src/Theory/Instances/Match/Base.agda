{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- Values (booleans and pairs) as a theory with no generators: every element
   of the free model is closed.  A bespoke `data Val` rather than the generic
   free model, so everything the checker touches reduces. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isOfHLevelRetract)
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns
module Theory.Instances.Match.Base where

open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.FinData.Properties using (isSetFin)
open import Cubical.Data.FinData.More using (two)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no ; Discrete)
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)
open import Cubical.Data.W.Indexed using (IW ; node ; isOfHLevelSuc-IW)

data VSort : Type ℓ-zero where
  val : VSort

data VOp : Type ℓ-zero where
  vtrueOp vfalseOp vpairOp : VOp

VAr : VOp → ℕ
VAr vtrueOp = 0
VAr vfalseOp = 0
VAr vpairOp = 2

VSortOf : (o : VOp) → Fin (VAr o) → VSort
VSortOf _ _ = val

VSig : SortedSig VSort ℓ-zero
VSig .ops = VOp
VSig .arity = VAr
VSig .sortOf = VSortOf
VSig .resultSort _ = val

VEqns : SortedEqns VSig ℓ-zero
VEqns .eqns = ⊥
VEqns .eqnSort ()
VEqns .varCount ()
VEqns .varSort ()
VEqns .lhs ()
VEqns .rhs ()

-- Named rather than `λ ()` at each use, so every downstream module is
-- instantiated at the *same* function and parameters match definitionally.
NoVar : Type ℓ-zero
NoVar = ⊥

noVarSort : NoVar → VSort
noVarSort ()

private
  opRep : VOp → Fin 3
  opRep vtrueOp = zero
  opRep vfalseOp = suc zero
  opRep vpairOp = suc (suc zero)

  opUnrep : Fin 3 → VOp
  opUnrep zero = vtrueOp
  opUnrep (suc zero) = vfalseOp
  opUnrep (suc (suc zero)) = vpairOp

  opRet : (o : VOp) → opUnrep (opRep o) ≡ o
  opRet vtrueOp = refl
  opRet vfalseOp = refl
  opRet vpairOp = refl

isSetVOp : isSet VOp
isSetVOp = isOfHLevelRetract 2 opRep opUnrep opRet isSetFin

private
  srtRet : (s : VSort) → val ≡ s
  srtRet val = refl

data Val : Type ℓ-zero where
  vtrue vfalse : Val
  vpair : Val → Val → Val

VCrr : VSort → Type ℓ-zero
VCrr val = Val

private
  Shape : VSort → Type ℓ-zero
  Shape val = VOp

  Pos : (s : VSort) → Shape s → Type ℓ-zero
  Pos val o = Fin (VAr o)

  sortAt : (s : VSort) (sh : Shape s) → Pos s sh → VSort
  sortAt val o a = VSortOf o a

  W : VSort → Type ℓ-zero
  W = IW Shape Pos sortAt

  isSetW : (s : VSort) → isSet (W s)
  isSetW = isOfHLevelSuc-IW 1 λ where val → isSetVOp

  toVal : Val → W val
  toVal vtrue = node vtrueOp λ ()
  toVal vfalse = node vfalseOp λ ()
  toVal (vpair v w) = node vpairOp (two (toVal v) (toVal w))

  toW : (s : VSort) → VCrr s → W s
  toW val = toVal

  fromVal : W val → Val
  fromVal (node vtrueOp _) = vtrue
  fromVal (node vfalseOp _) = vfalse
  fromVal (node vpairOp sub) =
    vpair (fromVal (sub zero)) (fromVal (sub (suc zero)))

  fromW : (s : VSort) → W s → VCrr s
  fromW val = fromVal

  valRet : (v : Val) → fromVal (toVal v) ≡ v
  valRet vtrue = refl
  valRet vfalse = refl
  valRet (vpair v w) = cong₂ vpair (valRet v) (valRet w)

  wRet : (s : VSort) (v : VCrr s) → fromW s (toW s v) ≡ v
  wRet val = valRet

isSetVCrr : (s : VSort) → isSet (VCrr s)
isSetVCrr s = isOfHLevelRetract 2 (toW s) (fromW s) (wRet s) (isSetW s)

open import Theory.Free.Base VEqns NoVar noVarSort

private
  vOps : Ops {σ = VSig} VCrr
  vOps vtrueOp _ = vtrue
  vOps vfalseOp _ = vfalse
  vOps vpairOp vs = vpair (vs zero) (vs (suc zero))

  vSat : (e : VEqns .eqns)
    (ρ : (w : vars VEqns e) → VCrr (VEqns .varSort e w))
    → TmRec VCrr vOps ρ (VEqns .lhs e) ≡ TmRec VCrr vOps ρ (VEqns .rhs e)
  vSat () ρ

  VModel : MOD VEqns ℓ-zero .ob
  VModel = (λ s → VCrr s , isSetVCrr s) , vOps , vSat

module Fold {ℓX} (X : VSort → Type ℓX) (α : Ops {σ = VSig} X) where

  foldVal : Val → X val
  foldVal vtrue = α vtrueOp λ ()
  foldVal vfalse = α vfalseOp λ ()
  foldVal (vpair v w) = α vpairOp (two (foldVal v) (foldVal w))

  fold : (s : VSort) → VCrr s → X s
  fold val = foldVal

  foldOp : (o : VOp) (vs : (a : Fin (VAr o)) → VCrr (VSortOf o a))
    → fold val (vOps o vs) ≡ α o (λ a → fold (VSortOf o a) (vs a))
  foldOp vtrueOp vs = cong (α vtrueOp) (funExt λ ())
  foldOp vfalseOp vs = cong (α vfalseOp) (funExt λ ())
  foldOp vpairOp vs = cong (α vpairOp) (funExt λ where
    zero → refl
    (suc zero) → refl)

  module _ (f : (s : VSort) → VCrr s → X s)
    (homf : (o : VOp) (vs : (a : Fin (VAr o)) → VCrr (VSortOf o a))
          → f val (vOps o vs) ≡ α o (λ a → f (VSortOf o a) (vs a))) where

    foldUniqVal : (v : Val) → f val v ≡ foldVal v
    foldUniqVal vtrue =
      homf vtrueOp (λ ()) ∙ cong (α vtrueOp) (funExt λ ())
    foldUniqVal vfalse =
      homf vfalseOp (λ ()) ∙ cong (α vfalseOp) (funExt λ ())
    foldUniqVal (vpair v w) =
        homf vpairOp (two v w)
      ∙ cong (α vpairOp) (funExt λ where
          zero → foldUniqVal v
          (suc zero) → foldUniqVal w)

    foldUniq : (s : VSort) (v : VCrr s) → f s v ≡ fold s v
    foldUniq val = foldUniqVal

vPresentation : FreePresentation ℓ-zero
vPresentation .P = VModel
vPresentation .satStrict () ρ
vPresentation .gen ()
vPresentation .rec {X = X} isSetX α sat ρ {s} = Fold.fold X α s
vPresentation .recGen isSetX α sat ρ ()
vPresentation .recOp {X = X} isSetX α sat ρ = Fold.foldOp X α
vPresentation .recUniq {X = X} isSetX α sat ρ f homf fβ {s} =
  Fold.foldUniq X α f homf s
