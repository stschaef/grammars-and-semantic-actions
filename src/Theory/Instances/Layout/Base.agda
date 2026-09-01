{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- Token streams as the free algebra on `{nilOp, consOp t}`: the token in
   the OPERATION makes the node cover LL(1) and every operation precise. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isOfHLevelRetract ; isSet×)
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns
module Theory.Instances.Layout.Base where

open import Cubical.Data.Empty using (⊥)
import Cubical.Data.Empty as Empty
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Nat using (ℕ ; isSetℕ)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr ; isSet⊎)
open import Cubical.Data.Unit using (Unit ; tt ; isSetUnit)
open import Cubical.Data.W.Indexed using (IW ; node ; isOfHLevelSuc-IW)

data TokKind : Type ℓ-zero where
  klet kwhere kin keq : TokKind
  kid : ℕ → TokKind

-- No line numbers: see `Offside`'s header for what that costs.
Tok : Type ℓ-zero
Tok = TokKind × ℕ

private
  kindRep : TokKind → Unit ⊎ (Unit ⊎ (Unit ⊎ (Unit ⊎ ℕ)))
  kindRep klet = inl tt
  kindRep kwhere = inr (inl tt)
  kindRep kin = inr (inr (inl tt))
  kindRep keq = inr (inr (inr (inl tt)))
  kindRep (kid n) = inr (inr (inr (inr n)))

  kindUnrep : Unit ⊎ (Unit ⊎ (Unit ⊎ (Unit ⊎ ℕ))) → TokKind
  kindUnrep (inl _) = klet
  kindUnrep (inr (inl _)) = kwhere
  kindUnrep (inr (inr (inl _))) = kin
  kindUnrep (inr (inr (inr (inl _)))) = keq
  kindUnrep (inr (inr (inr (inr n)))) = kid n

  kindRet : (k : TokKind) → kindUnrep (kindRep k) ≡ k
  kindRet klet = refl
  kindRet kwhere = refl
  kindRet kin = refl
  kindRet keq = refl
  kindRet (kid n) = refl

isSetTokKind : isSet TokKind
isSetTokKind = isOfHLevelRetract 2 kindRep kindUnrep kindRet
  (isSet⊎ isSetUnit (isSet⊎ isSetUnit (isSet⊎ isSetUnit (isSet⊎ isSetUnit isSetℕ))))

isSetTok : isSet Tok
isSetTok = isSet× isSetTokKind isSetℕ

-- One sort: every `⊗ᴰ` dependency is on the index, not a sibling slot.
data LSort : Type ℓ-zero where
  str : LSort

data LOp : Type ℓ-zero where
  nilOp : LOp
  consOp : Tok → LOp

Ar : LOp → ℕ
Ar nilOp = 0
Ar (consOp _) = 1

SortOf : (o : LOp) → Fin (Ar o) → LSort
SortOf _ _ = str

LSig : SortedSig LSort ℓ-zero
LSig .ops = LOp
LSig .arity = Ar
LSig .sortOf = SortOf
LSig .resultSort _ = str

LEqns : SortedEqns LSig ℓ-zero
LEqns .eqns = ⊥
LEqns .eqnSort ()
LEqns .varCount ()
LEqns .varSort ()
LEqns .lhs ()
LEqns .rhs ()

private
  opRep : LOp → Unit ⊎ Tok
  opRep nilOp = inl tt
  opRep (consOp t) = inr t

  opUnrep : Unit ⊎ Tok → LOp
  opUnrep (inl _) = nilOp
  opUnrep (inr t) = consOp t

  opRet : (o : LOp) → opUnrep (opRep o) ≡ o
  opRet nilOp = refl
  opRet (consOp t) = refl

isSetLOp : isSet LOp
isSetLOp = isOfHLevelRetract 2 opRep opUnrep opRet (isSet⊎ isSetUnit isSetTok)

private
  srtRep : LSort → Unit
  srtRep str = tt

  srtUnrep : Unit → LSort
  srtUnrep _ = str

  srtRet : (s : LSort) → srtUnrep (srtRep s) ≡ s
  srtRet str = refl

-- Bespoke `data` keeps the equations definitional and the tests `refl`.
data TokList : Type ℓ-zero where
  tnil : TokList
  tcons : Tok → TokList → TokList

Crr : LSort → Type ℓ-zero
Crr str = TokList

private
  Shape : LSort → Type ℓ-zero
  Shape str = LOp

  Pos : (s : LSort) → Shape s → Type ℓ-zero
  Pos str o = Fin (Ar o)

  sortAt : (s : LSort) (sh : Shape s) → Pos s sh → LSort
  sortAt str o a = SortOf o a

  W : LSort → Type ℓ-zero
  W = IW Shape Pos sortAt

  isSetW : (s : LSort) → isSet (W s)
  isSetW = isOfHLevelSuc-IW 1 λ where str → isSetLOp

  toTL : TokList → W str
  toTL tnil = node nilOp λ ()
  toTL (tcons t ts) = node (consOp t) λ _ → toTL ts

  toW : (s : LSort) → Crr s → W s
  toW str = toTL

  fromTL : W str → TokList
  fromTL (node nilOp sub) = tnil
  fromTL (node (consOp t) sub) = tcons t (fromTL (sub zero))

  fromW : (s : LSort) → W s → Crr s
  fromW str = fromTL

  tlRet : (ts : TokList) → fromTL (toTL ts) ≡ ts
  tlRet tnil = refl
  tlRet (tcons t ts) = cong (tcons t) (tlRet ts)

  wRet : (s : LSort) (x : Crr s) → fromW s (toW s x) ≡ x
  wRet str = tlRet

isSetCrr : (s : LSort) → isSet (Crr s)
isSetCrr s = isOfHLevelRetract 2 (toW s) (fromW s) (wRet s) (isSetW s)

-- Named, not `λ ()` at each use: absurd lambdas are not definitionally
-- equal, and every module in the chain needs the SAME one.
noVar : ⊥ → LSort
noVar ()

open import Theory.Free.Base LEqns ⊥ noVar

private
  lOps : Ops {σ = LSig} Crr
  lOps nilOp xs = tnil
  lOps (consOp t) xs = tcons t (xs zero)

  lSat : (e : LEqns .eqns)
    (ρ : (w : vars LEqns e) → Crr (LEqns .varSort e w))
    → TmRec Crr lOps ρ (LEqns .lhs e) ≡ TmRec Crr lOps ρ (LEqns .rhs e)
  lSat () ρ

  LModel : MOD LEqns ℓ-zero .ob
  LModel = (λ s → Crr s , isSetCrr s) , lOps , lSat

module Fold {ℓX} {X : LSort → Type ℓX} (α : Ops {σ = LSig} X) where

  foldTL : TokList → X str
  foldTL tnil = α nilOp λ ()
  foldTL (tcons t ts) = α (consOp t) λ _ → foldTL ts

  fold : (s : LSort) → Crr s → X s
  fold str = foldTL

  foldOp : (o : LOp) (ms : (a : Fin (Ar o)) → Crr (SortOf o a))
    → fold str (lOps o ms) ≡ α o (λ a → fold (SortOf o a) (ms a))
  foldOp nilOp ms = cong (α nilOp) (funExt λ ())
  foldOp (consOp t) ms = cong (α (consOp t)) (funExt λ where zero → refl)

  module _ (f : (s : LSort) → Crr s → X s)
    (homf : (o : LOp) (ms : (a : Fin (Ar o)) → Crr (SortOf o a))
          → f str (lOps o ms) ≡ α o (λ a → f (SortOf o a) (ms a))) where

    foldUniqTL : (ts : TokList) → f str ts ≡ foldTL ts
    foldUniqTL tnil = homf nilOp (λ ()) ∙ cong (α nilOp) (funExt λ ())
    foldUniqTL (tcons t ts) =
        homf (consOp t) (λ _ → ts)
      ∙ cong (α (consOp t)) (funExt λ where zero → foldUniqTL ts)

    foldUniq : (s : LSort) (m : Crr s) → f s m ≡ fold s m
    foldUniq str = foldUniqTL

lPresentation : FreePresentation ℓ-zero
lPresentation .P = LModel
lPresentation .satStrict () ρ
lPresentation .gen ()
lPresentation .rec {X = X} isSetX α sat ρ {s} = Fold.fold {X = X} α s
lPresentation .recGen isSetX α sat ρ ()
lPresentation .recOp {X = X} isSetX α sat ρ = Fold.foldOp {X = X} α
lPresentation .recUniq {X = X} isSetX α sat ρ f homf fβ {s} =
  Fold.foldUniq {X = X} α f homf s
