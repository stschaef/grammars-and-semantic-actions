{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isOfHLevelRetract)
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
module Theory.Instances.Lambda.TermPresentation
  (Name : Type ℓ-zero) (isSetName : isSet Name) where

open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.FinData.More using (two)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.W.Indexed using (IW ; node ; isOfHLevelSuc-IW)

open import Theory.Instances.Lambda.Signature
open import Theory.Free.Base λEqns Name (λ _ → nm)

private variable ℓX : Level

data RawTm : Type ℓ-zero where
  tvar : Name → RawTm
  tapp : RawTm → RawTm → RawTm
  tlam : Name → RawTm → RawTm

C : LSort → Type ℓ-zero
C nm = Name
C tm = RawTm

private
  Shape : LSort → Type ℓ-zero
  Shape nm = Name
  Shape tm = LOp

  Pos : (s : LSort) → Shape s → Type ℓ-zero
  Pos nm _ = ⊥
  Pos tm o = Fin (LAr o)

  sortAt : (s : LSort) (sh : Shape s) → Pos s sh → LSort
  sortAt tm o a = LSortOf o a

  W : LSort → Type ℓ-zero
  W = IW Shape Pos sortAt

  isSetW : (s : LSort) → isSet (W s)
  isSetW = isOfHLevelSuc-IW 1 λ where
    nm → isSetName
    tm → isSetLOp

  toNm : Name → W nm
  toNm x = node x (λ ())

  toTm : RawTm → W tm
  toTm (tvar x) = node varOp λ _ → toNm x
  toTm (tapp t u) = node appOp (two (toTm t) (toTm u))
  toTm (tlam x t) = node lamOp (two (toNm x) (toTm t))

  toW : (s : LSort) → C s → W s
  toW nm = toNm
  toW tm = toTm

  fromNm : W nm → Name
  fromNm (node x _) = x

  fromTm : W tm → RawTm
  fromTm (node varOp sub) = tvar (fromNm (sub zero))
  fromTm (node appOp sub) = tapp (fromTm (sub zero)) (fromTm (sub (suc zero)))
  fromTm (node lamOp sub) = tlam (fromNm (sub zero)) (fromTm (sub (suc zero)))

  fromW : (s : LSort) → W s → C s
  fromW nm = fromNm
  fromW tm = fromTm

  tmRet : (t : RawTm) → fromTm (toTm t) ≡ t
  tmRet (tvar x) = refl
  tmRet (tapp t u) = cong₂ tapp (tmRet t) (tmRet u)
  tmRet (tlam x t) = cong (tlam x) (tmRet t)

  wRet : (s : LSort) (x : C s) → fromW s (toW s x) ≡ x
  wRet nm x = refl
  wRet tm = tmRet

  isSetC : (s : LSort) → isSet (C s)
  isSetC s = isOfHLevelRetract 2 (toW s) (fromW s) (wRet s) (isSetW s)

  termOps : Ops {σ = λSig} C
  termOps varOp xs = tvar (xs zero)
  termOps appOp xs = tapp (xs zero) (xs (suc zero))
  termOps lamOp xs = tlam (xs zero) (xs (suc zero))

  termSat : (e : λEqns .eqns)
    (ρ : (w : vars λEqns e) → C (λEqns .varSort e w))
    → TmRec C termOps ρ (λEqns .lhs e) ≡ TmRec C termOps ρ (λEqns .rhs e)
  termSat () ρ

  TermModel : MOD λEqns ℓ-zero .ob
  TermModel = (λ s → C s , isSetC s) , termOps , termSat

module Fold {ℓX} {X : LSort → Type ℓX}
  (α : Ops {σ = λSig} X) (ρ : Name → X nm) where

  foldTm : RawTm → X tm
  foldTm (tvar x) = α varOp λ _ → ρ x
  foldTm (tapp t u) = α appOp (two (foldTm t) (foldTm u))
  foldTm (tlam x t) = α lamOp (two (ρ x) (foldTm t))

  fold : (s : LSort) → C s → X s
  fold nm = ρ
  fold tm = foldTm

  foldOp : (o : LOp) (ms : (a : Fin (LAr o)) → C (LSortOf o a))
    → fold tm (termOps o ms) ≡ α o (λ a → fold (LSortOf o a) (ms a))
  foldOp varOp ms = cong (α varOp) (funExt λ where zero → refl)
  foldOp appOp ms = cong (α appOp) (funExt λ where
    zero → refl
    (suc zero) → refl)
  foldOp lamOp ms = cong (α lamOp) (funExt λ where
    zero → refl
    (suc zero) → refl)

  module _ (f : (s : LSort) → C s → X s)
    (homf : (o : LOp) (ms : (a : Fin (LAr o)) → C (LSortOf o a))
          → f tm (termOps o ms) ≡ α o (λ a → f (LSortOf o a) (ms a)))
    (fβ : (v : Name) → f nm v ≡ ρ v) where

    foldUniqTm : (t : RawTm) → f tm t ≡ foldTm t
    foldUniqTm (tvar x) =
      homf varOp (λ _ → x) ∙ cong (α varOp) (funExt λ where zero → fβ x)
    foldUniqTm (tapp t u) =
        homf appOp (two t u)
      ∙ cong (α appOp) (funExt λ where
          zero → foldUniqTm t
          (suc zero) → foldUniqTm u)
    foldUniqTm (tlam x t) =
        homf lamOp (two x t)
      ∙ cong (α lamOp) (funExt λ where
          zero → fβ x
          (suc zero) → foldUniqTm t)

    foldUniq : (s : LSort) (m : C s) → f s m ≡ fold s m
    foldUniq nm x = fβ x
    foldUniq tm t = foldUniqTm t

termPresentation : FreePresentation ℓ-zero
termPresentation .P = TermModel
termPresentation .satStrict () ρ
termPresentation .gen v = v
termPresentation .rec isSetX α sat ρ {s} = Fold.fold α ρ s
termPresentation .recGen isSetX α sat ρ v = refl
termPresentation .recOp isSetX α sat ρ = Fold.foldOp α ρ
termPresentation .recUniq isSetX α sat ρ f homf fβ {s} =
  Fold.foldUniq α ρ f homf fβ s
