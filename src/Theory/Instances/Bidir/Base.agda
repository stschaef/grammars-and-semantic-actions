{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- The same simply typed lambda calculus as `Instances/Annotated`, with the
   application's annotation DELETED.

   `Annotated`'s signature has `appOp B` -- "apply, at argument type `B`" --
   and that index is the only reason its checking rule is syntax-directed:

     Γ ⊢ app[B] f a ⇐ A   iff   Γ ⊢ f ⇐ B ⇒ A  and  Γ ⊢ a ⇐ B

   Here `appOp` is a plain binary operation, so the rule can only be

     Γ ⊢ app f a ⇐ A      iff   ∃C. Γ ⊢ f ⇐ C, C = _ ⇒ A, Γ ⊢ a ⇐ dom C

   -- an existential over `Ty`, which is infinite.  `Annotated/Typing`'s
   header names that as the point where a checker needs `Route`, and
   `Instances/Bidir/Typing` is that checker.

   `lamOp B` KEEPS its annotation.  Without it the calculus is Curry-style
   and synthesis is unification, not a cover -- there would be no candidate
   type to route to, and the exercise would be vacuous.  With it every
   well-typed term has exactly one type, which is the theorem the route's
   obligation turns out to be.

   Everything below is `Annotated/Base` with `Ty` and the elaboration
   target `ATm` imported from there rather than duplicated: the point of
   the development is that a `BTm` elaborates to the `ATm` whose annotation
   was dropped, so the two calculi must speak of the same types. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isOfHLevelRetract ; isSet×)
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns
module Theory.Instances.Bidir.Base where

open import Cubical.Data.Bool using (Bool ; true ; false ; if_then_else_)
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

-- Types, and the annotated syntax, are `Annotated`'s.  Nothing else from
-- that module is in scope: it instantiates the framework at its own
-- presentation, and this one instantiates it at another.
open import Theory.Instances.Annotated.Base public using
  ( Ty ; ι ; _⇒_ ; IsArr ; isPropIsArr ; dom ; cod ; discreteTy ; isSetTyp
  ; ATm ; avar ; aapp ; alam )

-- The signature: `appOp` carries nothing.
data BSort : Type ℓ-zero where
  nm tm : BSort

data BOp : Type ℓ-zero where
  varOp : BOp
  appOp : BOp
  lamOp : Ty → BOp

Ar : BOp → ℕ
Ar varOp = 1
Ar appOp = 2
Ar (lamOp _) = 2

SortOf : (o : BOp) → Fin (Ar o) → BSort
SortOf varOp _ = nm
SortOf appOp _ = tm
SortOf (lamOp _) zero = nm
SortOf (lamOp _) (suc zero) = tm

BSig : SortedSig BSort ℓ-zero
BSig .ops = BOp
BSig .arity = Ar
BSig .sortOf = SortOf
BSig .resultSort _ = tm

BEqns : SortedEqns BSig ℓ-zero
BEqns .eqns = ⊥
BEqns .eqnSort ()
BEqns .varCount ()
BEqns .varSort ()
BEqns .lhs ()
BEqns .rhs ()

-- h-levels, for the term model.
private
  opRep : BOp → Unit ⊎ (Unit ⊎ Ty)
  opRep varOp = inl tt
  opRep appOp = inr (inl tt)
  opRep (lamOp B) = inr (inr B)

  opUnrep : Unit ⊎ (Unit ⊎ Ty) → BOp
  opUnrep (inl _) = varOp
  opUnrep (inr (inl _)) = appOp
  opUnrep (inr (inr B)) = lamOp B

  opRet : (o : BOp) → opUnrep (opRep o) ≡ o
  opRet varOp = refl
  opRet appOp = refl
  opRet (lamOp B) = refl

  isSetUnit' : isSet Unit
  isSetUnit' = Discrete→isSet λ _ _ → yes refl

isSetBOp : isSet BOp
isSetBOp = isOfHLevelRetract 2 opRep opUnrep opRet
  (isSet⊎ isSetUnit' (isSet⊎ isSetUnit' isSetTyp))

private
  srtRep : BSort → Bool
  srtRep nm = true
  srtRep tm = false

  srtUnrep : Bool → BSort
  srtUnrep true = nm
  srtUnrep false = tm

  srtRet : (s : BSort) → srtUnrep (srtRep s) ≡ s
  srtRet nm = refl
  srtRet tm = refl

  dBool : Discrete Bool
  dBool true true = yes refl
  dBool false false = yes refl
  dBool true false = no λ p → subst (λ b → if b then Unit else ⊥) p tt
  dBool false true = no λ p → subst (λ b → if b then ⊥ else Unit) p tt

isSetBSort : isSet BSort
isSetBSort =
  isOfHLevelRetract 2 srtRep srtUnrep srtRet (Discrete→isSet dBool)

-- The term model: a plain datatype, so that everything reduces.
data BTm : Type ℓ-zero where
  bvar : ℕ → BTm
  bapp : BTm → BTm → BTm
  blam : ℕ → Ty → BTm → BTm

Crr : BSort → Type ℓ-zero
Crr nm = ℕ
Crr tm = BTm

private
  Shape : BSort → Type ℓ-zero
  Shape nm = ℕ
  Shape tm = BOp

  Pos : (s : BSort) → Shape s → Type ℓ-zero
  Pos nm _ = ⊥
  Pos tm o = Fin (Ar o)

  sortAt : (s : BSort) (sh : Shape s) → Pos s sh → BSort
  sortAt tm o a = SortOf o a

  W : BSort → Type ℓ-zero
  W = IW Shape Pos sortAt

  isSetW : (s : BSort) → isSet (W s)
  isSetW = isOfHLevelSuc-IW 1 λ where
    nm → isSetℕ
    tm → isSetBOp

  toNm : ℕ → W nm
  toNm x = node x λ ()

  toTm : BTm → W tm
  toTm (bvar x) = node varOp λ _ → toNm x
  toTm (bapp f a) = node appOp (two (toTm f) (toTm a))
  toTm (blam x B t) = node (lamOp B) (two (toNm x) (toTm t))

  toW : (s : BSort) → Crr s → W s
  toW nm = toNm
  toW tm = toTm

  fromNm : W nm → ℕ
  fromNm (node x _) = x

  fromTm : W tm → BTm
  fromTm (node varOp sub) = bvar (fromNm (sub zero))
  fromTm (node appOp sub) = bapp (fromTm (sub zero)) (fromTm (sub (suc zero)))
  fromTm (node (lamOp B) sub) =
    blam (fromNm (sub zero)) B (fromTm (sub (suc zero)))

  fromW : (s : BSort) → W s → Crr s
  fromW nm = fromNm
  fromW tm = fromTm

  tmRet : (t : BTm) → fromTm (toTm t) ≡ t
  tmRet (bvar x) = refl
  tmRet (bapp f a) = cong₂ bapp (tmRet f) (tmRet a)
  tmRet (blam x B t) = cong (blam x B) (tmRet t)

  wRet : (s : BSort) (x : Crr s) → fromW s (toW s x) ≡ x
  wRet nm x = refl
  wRet tm = tmRet

isSetCrr : (s : BSort) → isSet (Crr s)
isSetCrr s = isOfHLevelRetract 2 (toW s) (fromW s) (wRet s) (isSetW s)

open import Theory.Free.Base BEqns ℕ (λ _ → nm)

private
  bOps : Ops {σ = BSig} Crr
  bOps varOp xs = bvar (xs zero)
  bOps appOp xs = bapp (xs zero) (xs (suc zero))
  bOps (lamOp B) xs = blam (xs zero) B (xs (suc zero))

  bSat : (e : BEqns .eqns)
    (ρ : (w : vars BEqns e) → Crr (BEqns .varSort e w))
    → TmRec Crr bOps ρ (BEqns .lhs e) ≡ TmRec Crr bOps ρ (BEqns .rhs e)
  bSat () ρ

  BModel : MOD BEqns ℓ-zero .ob
  BModel = (λ s → Crr s , isSetCrr s) , bOps , bSat

module Fold {ℓX} {X : BSort → Type ℓX}
  (α : Ops {σ = BSig} X) (ρ : ℕ → X nm) where

  foldTm : BTm → X tm
  foldTm (bvar x) = α varOp λ _ → ρ x
  foldTm (bapp f a) = α appOp (two (foldTm f) (foldTm a))
  foldTm (blam x B t) = α (lamOp B) (two (ρ x) (foldTm t))

  fold : (s : BSort) → Crr s → X s
  fold nm = ρ
  fold tm = foldTm

  foldOp : (o : BOp) (ms : (a : Fin (Ar o)) → Crr (SortOf o a))
    → fold tm (bOps o ms) ≡ α o (λ a → fold (SortOf o a) (ms a))
  foldOp varOp ms = cong (α varOp) (funExt λ where zero → refl)
  foldOp appOp ms = cong (α appOp) (funExt λ where
    zero → refl
    (suc zero) → refl)
  foldOp (lamOp B) ms = cong (α (lamOp B)) (funExt λ where
    zero → refl
    (suc zero) → refl)

  module _ (f : (s : BSort) → Crr s → X s)
    (homf : (o : BOp) (ms : (a : Fin (Ar o)) → Crr (SortOf o a))
          → f tm (bOps o ms) ≡ α o (λ a → f (SortOf o a) (ms a)))
    (fβ : (v : ℕ) → f nm v ≡ ρ v) where

    foldUniqTm : (t : BTm) → f tm t ≡ foldTm t
    foldUniqTm (bvar x) =
      homf varOp (λ _ → x) ∙ cong (α varOp) (funExt λ where zero → fβ x)
    foldUniqTm (bapp f' a) =
        homf appOp (two f' a)
      ∙ cong (α appOp) (funExt λ where
          zero → foldUniqTm f'
          (suc zero) → foldUniqTm a)
    foldUniqTm (blam x B t) =
        homf (lamOp B) (two x t)
      ∙ cong (α (lamOp B)) (funExt λ where
          zero → fβ x
          (suc zero) → foldUniqTm t)

    foldUniq : (s : BSort) (m : Crr s) → f s m ≡ fold s m
    foldUniq nm x = fβ x
    foldUniq tm t = foldUniqTm t

bPresentation : FreePresentation ℓ-zero
bPresentation .P = BModel
bPresentation .satStrict () ρ
bPresentation .gen v = v
bPresentation .rec isSetX α sat ρ {s} = Fold.fold α ρ s
bPresentation .recGen isSetX α sat ρ v = refl
bPresentation .recOp isSetX α sat ρ = Fold.foldOp α ρ
bPresentation .recUniq isSetX α sat ρ f homf fβ {s} =
  Fold.foldUniq α ρ f homf fβ s
