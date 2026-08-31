{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- What the generic combinators ask of the lambda theory: that every
   operation decompose uniquely, and that the arguments of a node sit below
   it in a well-founded order.

   Both are easier here than their monoid counterparts.  `Precise` is
   constructor injectivity for `RawTm` and holds of *every* operation --
   where over the free monoid it holds only of `literal c ⊗ -`, which is
   why that development has token rules rather than a node rule.  The order
   is the term's size; `Instances/Monoid/Suffix/Base` needs the proper
   suffix order and a length measure to justify the same `löb`, and
   `Later/Indexed` is generic enough that neither is re-proved here. -}
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

-- Names for the argument positions.  `arities σ o` is `Fin (σ .arity o)`,
-- so a slot is a numeral; these say which slot a numeral is, per operation.
-- They are pattern synonyms, so they work on both sides of a clause:
-- `Slots lamOp Γ ms theBody = ScopeSet (ms theBinder ∷ Γ)`.
pattern theVar    = zero        -- varOp: the name
pattern theFun    = zero        -- appOp: the function
pattern theArg    = suc zero    -- appOp: the argument
pattern theBinder = zero        -- lamOp: the bound name
pattern theBody   = suc zero    -- lamOp: the body under it

-- Constructor injectivity, by projection rather than by matching.
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

-- Every operation of `λSig` is precise: `op o ms` determines `ms`.
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

-- The measure the recursion descends on.
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

-- The subterm order, at whatever index type a checker family uses.  `rank`
-- breaks ties between components at the same term; nothing below needs it,
-- since every call this development makes is at a strictly smaller term.
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

-- The node cover: every term is a node of exactly one operation.
--
-- This is the free term algebra's answer to `Λ₁`, and it is the whole of
-- prediction here.  `total` is the algebra's induction principle and
-- `disjoint` is no-confusion, so one constructor of lookahead is always
-- enough -- there is no window, no width, and nothing to check.  Over the
-- free monoid the same two fields cost `Λ-total` and `Λ-disjoint`.
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
nodeCover .disjoint o o' ne m ((ms , e) , (ms' , e')) =
  Empty.rec (ne (Eq.pathToEq same))
  where
  same : o ≡ o'
  same = sym (clsL-node o ms)
       ∙ cong clsL (Eq.eqToPath e ∙ sym (Eq.eqToPath e'))
       ∙ clsL-node o' ms'
