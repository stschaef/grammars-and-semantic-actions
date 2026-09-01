{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Precision and guard order for the annotated lambda theory.  No
   `headClash`: `appOp B`/`lamOp B` give infinitely many operations, so a
   term unrolls to one node, not a sum over head constructors. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Type.Later.Indexed as LI
module Theory.Instances.Annotated.Guard where

open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-comm ; +-suc)
import Cubical.Data.Nat.Order as NO
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Sigma using (ΣPathP ; _,_ ; fst ; snd)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Annotated.Base public
open import Theory.Base AEqns ℕ (λ _ → nm) aPresentation public
open import Theory.Type.HLevels AEqns ℕ (λ _ → nm) aPresentation public
open import Theory.Type.Top.Base AEqns ℕ (λ _ → nm) aPresentation public
open import Theory.Type.Bottom.Base AEqns ℕ (λ _ → nm) aPresentation public
open import Theory.Type.Sum.Binary.Base AEqns ℕ (λ _ → nm) aPresentation public
open import Theory.Type.Product.Binary.Base AEqns ℕ (λ _ → nm) aPresentation public
open import Theory.Type.Cover.Base AEqns ℕ (λ _ → nm) aPresentation public
open import Theory.Type.Decidable.Base AEqns ℕ (λ _ → nm) aPresentation public
open import Theory.Combinator.Core AEqns ℕ (λ _ → nm) aPresentation public

private variable ℓX : Level

-- Slot names; pattern synonyms work on both sides of a clause.
pattern theVar    = zero        -- varOp:   the name
pattern theFun    = zero        -- appOp B: the function
pattern theArg    = suc zero    -- appOp B: the argument
pattern theBinder = zero        -- lamOp B: the bound name
pattern theBody   = suc zero    -- lamOp B: the body under it

-- Injectivity by projection: matching `Eq.refl` here is stuck without K
-- (`B` is both operation index and constructor argument).
varN : ℕ → ATm → ℕ
varN d (avar x) = x
varN d (aapp _ _ _) = d
varN d (alam _ _ _) = d
appFun appArgOf : ATm → ATm
appFun (avar x) = avar x
appFun (aapp _ f _) = f
appFun (alam x B t) = alam x B t
appArgOf (avar x) = avar x
appArgOf (aapp _ _ a) = a
appArgOf (alam x B t) = alam x B t

lamN : ℕ → ATm → ℕ
lamN d (avar _) = d
lamN d (aapp _ _ _) = d
lamN d (alam x _ _) = x

lamBd : ATm → ATm
lamBd (avar x) = avar x
lamBd (aapp B f a) = aapp B f a
lamBd (alam _ _ t) = t

preciseA : (o : AOp) → Precise o
preciseA varOp m (ms , e) (ms' , e') =
  ΣPathP (funExt slot , isProp→PathP (λ _ → isPropModelEq) e e')
  where
  whole : avar (ms zero) ≡ avar (ms' zero)
  whole = Eq.eqToPath e ∙ sym (Eq.eqToPath e')

  slot : (a : Fin 1) → ms a ≡ ms' a
  slot zero = cong (varN (ms zero)) whole
preciseA (appOp B) m (ms , e) (ms' , e') =
  ΣPathP (funExt slot , isProp→PathP (λ _ → isPropModelEq) e e')
  where
  whole : aapp B (ms zero) (ms (suc zero)) ≡ aapp B (ms' zero) (ms' (suc zero))
  whole = Eq.eqToPath e ∙ sym (Eq.eqToPath e')

  slot : (a : Fin 2) → ms a ≡ ms' a
  slot zero = cong appFun whole
  slot (suc zero) = cong appArgOf whole
preciseA (lamOp B) m (ms , e) (ms' , e') =
  ΣPathP (funExt slot , isProp→PathP (λ _ → isPropModelEq) e e')
  where
  whole : alam (ms zero) B (ms (suc zero)) ≡ alam (ms' zero) B (ms' (suc zero))
  whole = Eq.eqToPath e ∙ sym (Eq.eqToPath e')

  slot : (a : Fin 2) → ms a ≡ ms' a
  slot zero = cong (lamN (ms zero)) whole
  slot (suc zero) = cong lamBd whole

aSize : ATm → ℕ
aSize (avar _) = 1
aSize (aapp _ f a) = suc (aSize f + aSize a)
aSize (alam _ _ t) = suc (aSize t)

private
  fun< : (B : Ty) (f a : ATm) → aSize f NO.< aSize (aapp B f a)
  fun< B f a = aSize a , (+-suc (aSize a) (aSize f)
    ∙ cong suc (+-comm (aSize a) (aSize f)))

  arg< : (B : Ty) (f a : ATm) → aSize a NO.< aSize (aapp B f a)
  arg< B f a = aSize f , +-suc (aSize f) (aSize a)

  body< : (x : ℕ) (B : Ty) (t : ATm) → aSize t NO.< aSize (alam x B t)
  body< x B t = 0 , refl

module Subterm {X : Type ℓX} (isSetX : isSet X) (rank : X → ℕ) where

  srt : X → ASort
  srt _ = tm

  order : LI.IPtOrder AEqns ℕ (λ _ → nm) aPresentation srt ℓ-zero
  order = LI.ilexOrder AEqns ℕ (λ _ → nm) aPresentation srt
    isSetX (λ _ → aSize) rank

  open LI.IPtOrder order using (_<_) public

  smaller : {x x' : X} {t t' : ATm}
    → aSize t' NO.< aSize t → (x' , t') < (x , t)
  smaller lt = lift (Sum.inl lt)

  callFun : {x x' : X} (B : Ty) (f a : ATm) → (x' , f) < (x , aapp B f a)
  callFun B f a = smaller (fun< B f a)

  callArg : {x x' : X} (B : Ty) (f a : ATm) → (x' , a) < (x , aapp B f a)
  callArg B f a = smaller (arg< B f a)

  callBody : {x x' : X} (n : ℕ) (B : Ty) (t : ATm)
    → (x' , t) < (x , alam n B t)
  callBody n B t = smaller (body< n B t)

appArgs : (B : Ty) → ATm → ATm → (b : Fin 2) → ↓M (SortOf (appOp B) b)
appArgs B u v theFun = u
appArgs B u v theArg = v

lamArgs : (B : Ty) → ℕ → ATm → (b : Fin 2) → ↓M (SortOf (lamOp B) b)
lamArgs B y u theBinder = y
lamArgs B y u theBody = u

-- `AOp` is infinite: a cover does not care, a sum over the cells would.
clsA : ATm → AOp
clsA (avar _) = varOp
clsA (aapp B _ _) = appOp B
clsA (alam _ B _) = lamOp B

clsA-node : (o : AOp) (ms : interpIn o ↓M) → clsA (op o ms) ≡ o
clsA-node varOp ms = refl
clsA-node (appOp B) ms = refl
clsA-node (lamOp B) ms = refl

nodeCover : Cover AOp NodeAt
nodeCover .total (avar x) _ = varOp , ((λ _ → x) , Eq.refl)
nodeCover .total (aapp B f a) _ = appOp B , (appArgs B f a , Eq.refl)
nodeCover .total (alam x B t) _ = lamOp B , (lamArgs B x t , Eq.refl)
nodeCover .disjoint = clsDisjoint clsA λ o m (ms , e) →
  cong clsA (sym (Eq.eqToPath e)) ∙ clsA-node o ms
