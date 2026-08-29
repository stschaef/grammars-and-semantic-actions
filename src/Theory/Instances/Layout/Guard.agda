{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- What the generic combinators ask of the token-list theory: precision of
   every operation, and a well-founded order for the guard.

   The same two facts `Annotated/Guard` establishes, and for the same
   reason -- a free term algebra is precise everywhere and its subterm
   order is its size -- but degenerate in a way worth naming.  `consOp t`
   has one argument, so the "subterm order" is the proper *suffix* order
   and the measure is the length.  That is precisely the order the monoid
   development builds by hand out of `Suffix`; here it falls out of
   `ilexOrder` applied to the term size, because a token stream's only
   subterm is its tail.

   `LOp` is infinite -- `consOp` carries a token -- and, as in
   `Annotated/Guard`, a `Cover` does not care.  What would care is a *sum*
   over the cells; `Core`'s `Ans-map&` conditions on the cell instead. -}
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

-- The one argument position `consOp t` has.  `nilOp` has none, so its
-- slot function is an absurd pattern everywhere it appears.
pattern theTail = zero

-- Constructor injectivity, by projection rather than by matching, for the
-- reason `Annotated/Guard` gives: the token occurs both as the operation's
-- index and as a constructor argument, so `Eq.refl` on
-- `op (consOp t) ms ≡ tcons t ts` is stuck without K.
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

-- The measure: the number of tokens left to read.
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

-- Argument tuples.
consArgs : (t : Tok) → TokList → (b : Fin 1) → ↓M (SortOf (consOp t) b)
consArgs t ts theTail = ts

-- The node cover: by head constructor, which for a list is "empty or not,
-- and if not, which token".  `total` is list induction and `disjoint` is
-- no-confusion, so lookahead is one token wide by construction.
clsL : TokList → LOp
clsL tnil = nilOp
clsL (tcons t _) = consOp t

clsL-node : (o : LOp) (ms : interpIn o ↓M) → clsL (op o ms) ≡ o
clsL-node nilOp ms = refl
clsL-node (consOp t) ms = refl

nodeCover : Cover LOp NodeAt
nodeCover .total tnil _ = nilOp , ((λ ()) , Eq.refl)
nodeCover .total (tcons t ts) _ = consOp t , (consArgs t ts , Eq.refl)
nodeCover .disjoint o o' ne m ((ms , e) , (ms' , e')) =
  Empty.rec (ne (Eq.pathToEq same))
  where
  same : o ≡ o'
  same = sym (clsL-node o ms)
       ∙ cong clsL (Eq.eqToPath e ∙ sym (Eq.eqToPath e'))
       ∙ clsL-node o' ms'
