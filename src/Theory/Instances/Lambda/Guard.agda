{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Guard data for the lambda theory: `Precise` is constructor injectivity
   for `RawTm`; the well-founded order is term size. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Type.Later.Indexed as LI
module Theory.Instances.Lambda.Guard
  (Name : Type ℓ-zero) (isSetName : isSet Name) where

open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-comm ; +-suc)
import Cubical.Data.Nat.Order as NO
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Sigma using (ΣPathP ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
import Cubical.Data.Equality as Eq

open import Theory.Instances.Lambda.Base Name isSetName public
open import Theory.Type.HLevels λEqns Name (λ _ → nm) termPresentation public
open import Theory.Type.Top.Base λEqns Name (λ _ → nm) termPresentation public
open import Theory.Type.Sum.Binary.Base λEqns Name (λ _ → nm) termPresentation public
open import Theory.Type.Product.Binary.Base λEqns Name (λ _ → nm) termPresentation public
open import Theory.Type.Bottom.Base λEqns Name (λ _ → nm) termPresentation public
open import Theory.Type.Cover.Base λEqns Name (λ _ → nm) termPresentation public
open import Theory.Type.Decidable.Base λEqns Name (λ _ → nm) termPresentation public
open import Theory.Combinator.Core λEqns Name (λ _ → nm) termPresentation public

private variable ℓX : Level

-- Pattern synonyms naming argument positions, usable on both sides of a
-- clause: `Slots lamOp Γ ms theBody = ScopeSet (ms theBinder ∷ Γ)`.
pattern theVar    = zero        -- varOp: the name
pattern theFun    = zero        -- appOp: the function
pattern theArg    = suc zero    -- appOp: the argument
pattern theBinder = zero        -- lamOp: the bound name
pattern theBody   = suc zero    -- lamOp: the body under it

-- injectivity by projection rather than by matching
private
  nameOf : Name → RawTm → Name
  nameOf d (tvar x) = x
  nameOf d (tapp _ _) = d
  nameOf d (tlam _ _) = d

  funOf : RawTm → RawTm
  funOf (tvar x) = tvar x
  funOf (tapp t _) = t
  funOf (tlam x t) = tlam x t

  argOf : RawTm → RawTm
  argOf (tvar x) = tvar x
  argOf (tapp _ u) = u
  argOf (tlam x t) = tlam x t

  binderOf : Name → RawTm → Name
  binderOf d (tvar _) = d
  binderOf d (tapp _ _) = d
  binderOf d (tlam x _) = x

  bodyOf : RawTm → RawTm
  bodyOf (tvar x) = tvar x
  bodyOf (tapp t u) = tapp t u
  bodyOf (tlam _ t) = t

-- Precision: `op o ms` determines `ms`.
preciseλ : (o : LOp) → Precise o
preciseλ varOp m (ms , e) (ms' , e') =
  ΣPathP (funExt slot , isProp→PathP (λ _ → isPropModelEq) e e')
  where
  whole : tvar (ms zero) ≡ tvar (ms' zero)
  whole = Eq.eqToPath e ∙ sym (Eq.eqToPath e')

  slot : (a : Fin 1) → ms a ≡ ms' a
  slot zero = cong (nameOf (ms zero)) whole
preciseλ appOp m (ms , e) (ms' , e') =
  ΣPathP (funExt slot , isProp→PathP (λ _ → isPropModelEq) e e')
  where
  whole : tapp (ms zero) (ms (suc zero)) ≡ tapp (ms' zero) (ms' (suc zero))
  whole = Eq.eqToPath e ∙ sym (Eq.eqToPath e')

  slot : (a : Fin 2) → ms a ≡ ms' a
  slot zero = cong funOf whole
  slot (suc zero) = cong argOf whole
preciseλ lamOp m (ms , e) (ms' , e') =
  ΣPathP (funExt slot , isProp→PathP (λ _ → isPropModelEq) e e')
  where
  whole : tlam (ms zero) (ms (suc zero)) ≡ tlam (ms' zero) (ms' (suc zero))
  whole = Eq.eqToPath e ∙ sym (Eq.eqToPath e')

  slot : (a : Fin 2) → ms a ≡ ms' a
  slot zero = cong (binderOf (ms zero)) whole
  slot (suc zero) = cong bodyOf whole

tmSize : RawTm → ℕ
tmSize (tvar _) = 1
tmSize (tapp t u) = suc (tmSize t + tmSize u)
tmSize (tlam _ t) = suc (tmSize t)

private
  n<sn : (n : ℕ) → n NO.< suc n
  n<sn n = 0 , refl

  fun< : (t u : RawTm) → tmSize t NO.< tmSize (tapp t u)
  fun< t u = tmSize u , (+-suc (tmSize u) (tmSize t)
    ∙ cong suc (+-comm (tmSize u) (tmSize t)))

  arg< : (t u : RawTm) → tmSize u NO.< tmSize (tapp t u)
  arg< t u = tmSize t , +-suc (tmSize t) (tmSize u)

  body< : (x : Name) (t : RawTm) → tmSize t NO.< tmSize (tlam x t)
  body< x t = n<sn (tmSize t)

-- `rank` breaks ties between components at the same term; unused below,
-- since every call here is at a strictly smaller term.
module Subterm {X : Type ℓX} (isSetX : isSet X) (rank : X → ℕ) where

  srt : X → LSort
  srt _ = tm

  order : LI.IPtOrder λEqns Name (λ _ → nm) termPresentation srt ℓ-zero
  order = LI.ilexOrder λEqns Name (λ _ → nm) termPresentation srt
    isSetX (λ _ → tmSize) rank

  open LI.IPtOrder order using (_<_) public

  smaller : {x x' : X} {t t' : RawTm}
    → tmSize t' NO.< tmSize t → (x' , t') < (x , t)
  smaller lt = lift (Sum.inl lt)

  callFun : {x x' : X} (t u : RawTm) → (x' , t) < (x , tapp t u)
  callFun t u = smaller (fun< t u)

  callArg : {x x' : X} (t u : RawTm) → (x' , u) < (x , tapp t u)
  callArg t u = smaller (arg< t u)

  callBody : {x x' : X} (n : Name) (t : RawTm) → (x' , t) < (x , tlam n t)
  callBody n t = smaller (body< n t)

-- Node cover: `total` is the induction principle, `disjoint` is
-- no-confusion, so one constructor of lookahead always suffices.
clsL : RawTm → LOp
clsL (tvar _) = varOp
clsL (tapp _ _) = appOp
clsL (tlam _ _) = lamOp

clsL-node : (o : LOp) (ms : interpIn o ↓M) → clsL (op o ms) ≡ o
clsL-node varOp ms = refl
clsL-node appOp ms = refl
clsL-node lamOp ms = refl

nodeCover : Cover LOp NodeAt
nodeCover .total (tvar x) _ = varOp , ((λ _ → x) , Eq.refl)
nodeCover .total (tapp t u) _ = appOp , (appArgs t u , Eq.refl)
nodeCover .total (tlam x t) _ = lamOp , (lamArgs x t , Eq.refl)
nodeCover .disjoint = clsDisjoint clsL λ o m (ms , e) →
  cong clsL (sym (Eq.eqToPath e)) ∙ clsL-node o ms
