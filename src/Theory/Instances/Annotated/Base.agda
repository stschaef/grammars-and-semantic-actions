{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- A simply typed lambda calculus with annotated application, as a theory.

   Two sorts and three operations, where the operations are *indexed by
   external data*: `appOp B` is "apply, at argument type `B`" and `lamOp B`
   is "abstract, at domain `B`".  That is how an annotation enters a
   signature, and it is what makes the calculus syntax-directed:

     Γ ⊢ var x        ⇐ A   iff  Γ(x) = A
     Γ ⊢ app[B] f a   ⇐ A   iff  Γ ⊢ f ⇐ B ⇒ A  and  Γ ⊢ a ⇐ B
     Γ ⊢ lam[B] x t   ⇐ A   iff  A = B ⇒ C  and  Γ,x:B ⊢ t ⇐ C

   Every premise's type is determined by the conclusion's plus the node's
   annotation, so there is no existential and no synthesis mode.  Dropping
   `B` from `appOp` puts one back -- `Γ ⊢ f ⇐ ? ⇒ A` -- and that is exactly
   the point at which a checker needs `Route`; see `Typing`'s header. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isOfHLevelRetract ; isSet× )
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns
module Theory.Instances.Annotated.Base where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Empty using (⊥)
import Cubical.Data.Empty as Empty
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.FinData.Properties using (isSetFin)
open import Cubical.Data.FinData.More using (two)
open import Cubical.Data.Nat using (ℕ ; isSetℕ ; discreteℕ)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr ; isSet⊎)
open import Cubical.Data.Unit using (Unit ; tt ; Unit* ; tt*)
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no ; Discrete)
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)
open import Cubical.Data.W.Indexed using (IW ; node ; isOfHLevelSuc-IW)

-- Types, external to the theory: they annotate operations rather than
-- occupying a sort, so type equality stays a plain decidable equality.
infixr 25 _⇒_
data Ty : Type ℓ-zero where
  ι : Ty
  _⇒_ : Ty → Ty → Ty

-- Viewing a type as an arrow.  `IsArr` is a proposition and `dom`/`cod`
-- are total, so "A is an arrow with domain B" is `IsArr A × (dom A ≡ B)` --
-- a proposition, decidable, and usable as a slot of a node.
IsArr : Ty → Type ℓ-zero
IsArr ι = ⊥
IsArr (_ ⇒ _) = Unit

isPropIsArr : (A : Ty) → isProp (IsArr A)
isPropIsArr ι = λ ()
isPropIsArr (_ ⇒ _) = λ _ _ → refl

dom cod : Ty → Ty
dom ι = ι
dom (B ⇒ _) = B
cod ι = ι
cod (_ ⇒ C) = C

discreteTy : Discrete Ty
discreteTy ι ι = yes refl
discreteTy ι (B ⇒ C) = no λ p → subst IsArr (sym p) tt
discreteTy (B ⇒ C) ι = no λ p → subst IsArr p tt
discreteTy (B ⇒ C) (B' ⇒ C') = onParts (discreteTy B B') (discreteTy C C')
  where
  onParts : Dec (B ≡ B') → Dec (C ≡ C') → Dec ((B ⇒ C) ≡ (B' ⇒ C'))
  onParts (yes p) (yes q) = yes (cong₂ _⇒_ p q)
  onParts (no ¬p) _ = no λ e → ¬p (cong dom e)
  onParts _ (no ¬q) = no λ e → ¬q (cong cod e)

isSetTyp : isSet Ty
isSetTyp = Discrete→isSet discreteTy

-- The signature.
data ASort : Type ℓ-zero where
  nm tm : ASort

data AOp : Type ℓ-zero where
  varOp : AOp
  appOp : Ty → AOp
  lamOp : Ty → AOp

Ar : AOp → ℕ
Ar varOp = 1
Ar (appOp _) = 2
Ar (lamOp _) = 2

SortOf : (o : AOp) → Fin (Ar o) → ASort
SortOf varOp _ = nm
SortOf (appOp _) _ = tm
SortOf (lamOp _) zero = nm
SortOf (lamOp _) (suc zero) = tm

ASig : SortedSig ASort ℓ-zero
ASig .ops = AOp
ASig .arity = Ar
ASig .sortOf = SortOf
ASig .resultSort _ = tm

AEqns : SortedEqns ASig ℓ-zero
AEqns .eqns = ⊥
AEqns .eqnSort ()
AEqns .varCount ()
AEqns .varSort ()
AEqns .lhs ()
AEqns .rhs ()

-- h-levels, for the term model.
private
  opRep : AOp → Unit ⊎ (Ty ⊎ Ty)
  opRep varOp = inl tt
  opRep (appOp B) = inr (inl B)
  opRep (lamOp B) = inr (inr B)

  opUnrep : Unit ⊎ (Ty ⊎ Ty) → AOp
  opUnrep (inl _) = varOp
  opUnrep (inr (inl B)) = appOp B
  opUnrep (inr (inr B)) = lamOp B

  opRet : (o : AOp) → opUnrep (opRep o) ≡ o
  opRet varOp = refl
  opRet (appOp B) = refl
  opRet (lamOp B) = refl

isSetAOp : isSet AOp
isSetAOp = isOfHLevelRetract 2 opRep opUnrep opRet
  (isSet⊎ (Discrete→isSet (λ _ _ → yes refl)) (isSet⊎ isSetTyp isSetTyp))

private
  srtRep : ASort → Bool
  srtRep nm = true
  srtRep tm = false

  srtUnrep : Bool → ASort
  srtUnrep true = nm
  srtUnrep false = tm

  srtRet : (s : ASort) → srtUnrep (srtRep s) ≡ s
  srtRet nm = refl
  srtRet tm = refl

isSetASort : isSet ASort
isSetASort = isOfHLevelRetract 2 srtRep srtUnrep srtRet
  (Discrete→isSet dBool)
  where
  dBool : Discrete Bool
  dBool true true = yes refl
  dBool false false = yes refl
  dBool true false = no λ p → subst (λ b → if b then Unit else ⊥) p tt
    where open import Cubical.Data.Bool using (if_then_else_)
  dBool false true = no λ p → subst (λ b → if b then ⊥ else Unit) p tt
    where open import Cubical.Data.Bool using (if_then_else_)

-- The term model: a plain datatype, so that everything reduces.
data ATm : Type ℓ-zero where
  avar : ℕ → ATm
  aapp : Ty → ATm → ATm → ATm
  alam : ℕ → Ty → ATm → ATm

Crr : ASort → Type ℓ-zero
Crr nm = ℕ
Crr tm = ATm

private
  Shape : ASort → Type ℓ-zero
  Shape nm = ℕ
  Shape tm = AOp

  Pos : (s : ASort) → Shape s → Type ℓ-zero
  Pos nm _ = ⊥
  Pos tm o = Fin (Ar o)

  sortAt : (s : ASort) (sh : Shape s) → Pos s sh → ASort
  sortAt tm o a = SortOf o a

  W : ASort → Type ℓ-zero
  W = IW Shape Pos sortAt

  isSetW : (s : ASort) → isSet (W s)
  isSetW = isOfHLevelSuc-IW 1 λ where
    nm → isSetℕ
    tm → isSetAOp

  toNm : ℕ → W nm
  toNm x = node x λ ()

  toTm : ATm → W tm
  toTm (avar x) = node varOp λ _ → toNm x
  toTm (aapp B f a) = node (appOp B) (two (toTm f) (toTm a))
  toTm (alam x B t) = node (lamOp B) (two (toNm x) (toTm t))

  toW : (s : ASort) → Crr s → W s
  toW nm = toNm
  toW tm = toTm

  fromNm : W nm → ℕ
  fromNm (node x _) = x

  fromTm : W tm → ATm
  fromTm (node varOp sub) = avar (fromNm (sub zero))
  fromTm (node (appOp B) sub) = aapp B (fromTm (sub zero)) (fromTm (sub (suc zero)))
  fromTm (node (lamOp B) sub) = alam (fromNm (sub zero)) B (fromTm (sub (suc zero)))

  fromW : (s : ASort) → W s → Crr s
  fromW nm = fromNm
  fromW tm = fromTm

  tmRet : (t : ATm) → fromTm (toTm t) ≡ t
  tmRet (avar x) = refl
  tmRet (aapp B f a) = cong₂ (aapp B) (tmRet f) (tmRet a)
  tmRet (alam x B t) = cong (alam x B) (tmRet t)

  wRet : (s : ASort) (x : Crr s) → fromW s (toW s x) ≡ x
  wRet nm x = refl
  wRet tm = tmRet

isSetCrr : (s : ASort) → isSet (Crr s)
isSetCrr s = isOfHLevelRetract 2 (toW s) (fromW s) (wRet s) (isSetW s)

open import Theory.Free.Base AEqns ℕ (λ _ → nm)

private
  aOps : Ops {σ = ASig} Crr
  aOps varOp xs = avar (xs zero)
  aOps (appOp B) xs = aapp B (xs zero) (xs (suc zero))
  aOps (lamOp B) xs = alam (xs zero) B (xs (suc zero))

  aSat : (e : AEqns .eqns)
    (ρ : (w : vars AEqns e) → Crr (AEqns .varSort e w))
    → TmRec Crr aOps ρ (AEqns .lhs e) ≡ TmRec Crr aOps ρ (AEqns .rhs e)
  aSat () ρ

  AModel : MOD AEqns ℓ-zero .ob
  AModel = (λ s → Crr s , isSetCrr s) , aOps , aSat

module Fold {ℓX} {X : ASort → Type ℓX}
  (α : Ops {σ = ASig} X) (ρ : ℕ → X nm) where

  foldTm : ATm → X tm
  foldTm (avar x) = α varOp λ _ → ρ x
  foldTm (aapp B f a) = α (appOp B) (two (foldTm f) (foldTm a))
  foldTm (alam x B t) = α (lamOp B) (two (ρ x) (foldTm t))

  fold : (s : ASort) → Crr s → X s
  fold nm = ρ
  fold tm = foldTm

  foldOp : (o : AOp) (ms : (a : Fin (Ar o)) → Crr (SortOf o a))
    → fold tm (aOps o ms) ≡ α o (λ a → fold (SortOf o a) (ms a))
  foldOp varOp ms = cong (α varOp) (funExt λ where zero → refl)
  foldOp (appOp B) ms = cong (α (appOp B)) (funExt λ where
    zero → refl
    (suc zero) → refl)
  foldOp (lamOp B) ms = cong (α (lamOp B)) (funExt λ where
    zero → refl
    (suc zero) → refl)

  module _ (f : (s : ASort) → Crr s → X s)
    (homf : (o : AOp) (ms : (a : Fin (Ar o)) → Crr (SortOf o a))
          → f tm (aOps o ms) ≡ α o (λ a → f (SortOf o a) (ms a)))
    (fβ : (v : ℕ) → f nm v ≡ ρ v) where

    foldUniqTm : (t : ATm) → f tm t ≡ foldTm t
    foldUniqTm (avar x) =
      homf varOp (λ _ → x) ∙ cong (α varOp) (funExt λ where zero → fβ x)
    foldUniqTm (aapp B f' a) =
        homf (appOp B) (two f' a)
      ∙ cong (α (appOp B)) (funExt λ where
          zero → foldUniqTm f'
          (suc zero) → foldUniqTm a)
    foldUniqTm (alam x B t) =
        homf (lamOp B) (two x t)
      ∙ cong (α (lamOp B)) (funExt λ where
          zero → fβ x
          (suc zero) → foldUniqTm t)

    foldUniq : (s : ASort) (m : Crr s) → f s m ≡ fold s m
    foldUniq nm x = fβ x
    foldUniq tm t = foldUniqTm t

aPresentation : FreePresentation ℓ-zero
aPresentation .P = AModel
aPresentation .satStrict () ρ
aPresentation .gen v = v
aPresentation .rec isSetX α sat ρ {s} = Fold.fold α ρ s
aPresentation .recGen isSetX α sat ρ v = refl
aPresentation .recOp isSetX α sat ρ = Fold.foldOp α ρ
aPresentation .recUniq isSetX α sat ρ f homf fβ {s} =
  Fold.foldUniq α ρ f homf fβ s
