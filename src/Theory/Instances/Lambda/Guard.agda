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
open import Theory.Combinator.Core λEqns Name (λ _ → nm) termPresentation public

private variable ℓX : Level

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

-- No confusion.  A node's head is its operation, so a node whose operation
-- does not match the term's head constructor has no inhabitant -- which is
-- what a checker needs to *refute* the branches it did not take.  Over the
-- free monoid this is `Λ-disjoint`, a page of reasoning about splittings;
-- here it is `refl` three times.
data Hd : Type ℓ-zero where
  hvar happ hlam : Hd

hdOf : RawTm → Hd
hdOf (tvar _) = hvar
hdOf (tapp _ _) = happ
hdOf (tlam _ _) = hlam

hdOfOp : LOp → Hd
hdOfOp varOp = hvar
hdOfOp appOp = happ
hdOfOp lamOp = hlam

hdOfNode : (o : LOp) (ms : interpIn o ↓M) → hdOf (op o ms) ≡ hdOfOp o
hdOfNode varOp ms = refl
hdOfNode appOp ms = refl
hdOfNode lamOp ms = refl

-- `HdCode a b` is `Unit` when the heads agree and `⊥` when they differ, so
-- "these two constructors are distinct" is a definitional fact rather than
-- an appeal to an absurd pattern -- which cubical does not give for paths.
HdCode : Hd → Hd → Type ℓ-zero
HdCode hvar hvar = Unit
HdCode hvar happ = Empty.⊥
HdCode hvar hlam = Empty.⊥
HdCode happ hvar = Empty.⊥
HdCode happ happ = Unit
HdCode happ hlam = Empty.⊥
HdCode hlam hvar = Empty.⊥
HdCode hlam happ = Empty.⊥
HdCode hlam hlam = Unit

private
  hdRefl : (a : Hd) → HdCode a a
  hdRefl hvar = tt
  hdRefl happ = tt
  hdRefl hlam = tt

hdEncode : {a b : Hd} → a ≡ b → HdCode a b
hdEncode {a = a} p = subst (HdCode a) p (hdRefl a)

-- `o`'s node cannot sit at a term with a different head.  Over the free
-- monoid the counterpart is `Λ-disjoint`, a page of reasoning about how a
-- word splits; here the caller passes the identity.
headClash : (o : LOp) (m : RawTm)
  → (HdCode (hdOfOp o) (hdOf m) → Empty.⊥)
  → (ms : interpIn o ↓M) → op o ms Eq.≡ m → Empty.⊥
headClash o m clash ms e =
  clash (hdEncode (sym (hdOfNode o ms) ∙ cong hdOf (Eq.eqToPath e)))
