{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Precision and guard order for the token-list theory.  The subterm order
   is the proper suffix order, via `ilexOrder` on length.  `LOp` is
   infinite; a cover does not care, a sum over the cells would. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Type.Later.Indexed as LI
module Theory.Instances.Layout.Guard where

open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NO
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Sigma using (ΣPathP ; _,_ ; fst ; snd)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Layout.Base public
open import Theory.Base LEqns ⊥ noVar lPresentation public
open import Theory.Type.HLevels LEqns ⊥ noVar lPresentation public
open import Theory.Type.Top.Base LEqns ⊥ noVar lPresentation public
open import Theory.Type.Bottom.Base LEqns ⊥ noVar lPresentation public
open import Theory.Type.Sum.Binary.Base LEqns ⊥ noVar lPresentation public
open import Theory.Type.Product.Binary.Base LEqns ⊥ noVar lPresentation public
open import Theory.Type.Cover.Base LEqns ⊥ noVar lPresentation public
open import Theory.Type.Decidable.Base LEqns ⊥ noVar lPresentation public
open import Theory.Combinator.Core LEqns ⊥ noVar lPresentation public

private variable ℓX : Level

pattern theTail = zero

-- Injectivity by projection, for the reason `Annotated/Guard` gives.
tlOf : TokList → TokList
tlOf tnil = tnil
tlOf (tcons _ ts) = ts

preciseL : (o : LOp) → Precise o
preciseL nilOp m (ms , e) (ms' , e') =
  ΣPathP (funExt (λ ()) , isProp→PathP (λ _ → isPropModelEq) e e')
preciseL (consOp t) m (ms , e) (ms' , e') =
  ΣPathP (funExt slot , isProp→PathP (λ _ → isPropModelEq) e e')
  where
  whole : tcons t (ms zero) ≡ tcons t (ms' zero)
  whole = Eq.eqToPath e ∙ sym (Eq.eqToPath e')

  slot : (a : Fin 1) → ms a ≡ ms' a
  slot zero = cong tlOf whole

lSize : TokList → ℕ
lSize tnil = 0
lSize (tcons _ ts) = suc (lSize ts)

private
  tail< : (t : Tok) (ts : TokList) → lSize ts NO.< lSize (tcons t ts)
  tail< t ts = 0 , refl

module Subterm {X : Type ℓX} (isSetX : isSet X) (rank : X → ℕ) where

  srt : X → LSort
  srt _ = str

  order : LI.IPtOrder LEqns ⊥ noVar lPresentation srt ℓ-zero
  order = LI.ilexOrder LEqns ⊥ noVar lPresentation srt
    isSetX (λ _ → lSize) rank

  open LI.IPtOrder order using (_<_) public

  smaller : {x x' : X} {ts ts' : TokList}
    → lSize ts' NO.< lSize ts → (x' , ts') < (x , ts)
  smaller lt = lift (Sum.inl lt)

  callTail : {x x' : X} (t : Tok) (ts : TokList) → (x' , ts) < (x , tcons t ts)
  callTail t ts = smaller (tail< t ts)

consArgs : (t : Tok) → TokList → (b : Fin 1) → ↓M (SortOf (consOp t) b)
consArgs t ts theTail = ts

-- Cover by head constructor: lookahead is one token by construction.
clsL : TokList → LOp
clsL tnil = nilOp
clsL (tcons t _) = consOp t

clsL-node : (o : LOp) (ms : interpIn o ↓M) → clsL (op o ms) ≡ o
clsL-node nilOp ms = refl
clsL-node (consOp t) ms = refl

nodeCover : Cover LOp NodeAt
nodeCover .total tnil _ = nilOp , ((λ ()) , Eq.refl)
nodeCover .total (tcons t ts) _ = consOp t , (consArgs t ts , Eq.refl)
nodeCover .disjoint = clsDisjoint clsL λ o m (ms , e) →
  cong clsL (sym (Eq.eqToPath e)) ∙ clsL-node o ms
