{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- What the combinators ask of the chosen-head theory -- exactly what
   `Bag/Failure` proves the commutative theory cannot supply
   (`preciseC` vs `¬preciseNode`, `nodeCover` vs `¬disjointHead`). -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Type.Later.Indexed as LI
module Theory.Instances.Bag.Chosen.Guard
  (El : Type ℓ-zero) (isSetEl : isSet El) where

open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NO
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Sigma using (ΣPathP ; _,_ ; fst ; snd)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Bag.Chosen.Base El isSetEl public
open import Theory.Base CEqns ⊥ noVar cPresentation public
open import Theory.Type.HLevels CEqns ⊥ noVar cPresentation public
open import Theory.Type.Top.Base CEqns ⊥ noVar cPresentation public
open import Theory.Type.Bottom.Base CEqns ⊥ noVar cPresentation public
open import Theory.Type.Sum.Binary.Base CEqns ⊥ noVar cPresentation public
open import Theory.Type.Product.Binary.Base CEqns ⊥ noVar cPresentation public
open import Theory.Type.Cover.Base CEqns ⊥ noVar cPresentation public
open import Theory.Type.Decidable.Base CEqns ⊥ noVar cPresentation public
open import Theory.Combinator.Core CEqns ⊥ noVar cPresentation public

private variable ℓX : Level

-- `consOp x`'s one argument slot; `nilOp` has none.
pattern theRest = zero

-- Injectivity by projection: matching `Eq.refl` on `op (consOp x) ms ≡ x ∷ l`
-- is stuck without K.
tlOf : List El → List El
tlOf [] = []
tlOf (_ ∷ l) = l

preciseC : (o : COp) → Precise o
preciseC nilOp m (ms , e) (ms' , e') =
  ΣPathP (funExt (λ ()) , isProp→PathP (λ _ → isPropModelEq) e e')
preciseC (consOp x) m (ms , e) (ms' , e') =
  ΣPathP (funExt slot , isProp→PathP (λ _ → isPropModelEq) e e')
  where
  whole : x ∷ ms zero ≡ x ∷ ms' zero
  whole = Eq.eqToPath e ∙ sym (Eq.eqToPath e')

  slot : (a : Fin 1) → ms a ≡ ms' a
  slot zero = cong tlOf whole

cSize : List El → ℕ
cSize [] = 0
cSize (_ ∷ l) = suc (cSize l)

private
  rest< : (x : El) (l : List El) → cSize l NO.< cSize (x ∷ l)
  rest< x l = 0 , refl

module Subbag {X : Type ℓX} (isSetX : isSet X) (rank : X → ℕ) where

  srt : X → CSort
  srt _ = bag

  order : LI.IPtOrder CEqns ⊥ noVar cPresentation srt ℓ-zero
  order = LI.ilexOrder CEqns ⊥ noVar cPresentation srt
    isSetX (λ _ → cSize) rank

  open LI.IPtOrder order using (_<_) public

  smaller : {x x' : X} {l l' : List El}
    → cSize l' NO.< cSize l → (x' , l') < (x , l)
  smaller lt = lift (Sum.inl lt)

  callRest : {i i' : X} (x : El) (l : List El) → (i' , l) < (i , x ∷ l)
  callRest x l = smaller (rest< x l)

consArgs : (x : El) → List El → (b : Fin 1) → ↓M (CSortOf (consOp x) b)
consArgs x l theRest = l

-- the node cover, by head constructor
clsC : List El → COp
clsC [] = nilOp
clsC (x ∷ _) = consOp x

clsC-node : (o : COp) (ms : interpIn o ↓M) → clsC (op o ms) ≡ o
clsC-node nilOp ms = refl
clsC-node (consOp x) ms = refl

nodeCover : Cover COp NodeAt
nodeCover .total [] _ = nilOp , ((λ ()) , Eq.refl)
nodeCover .total (x ∷ l) _ = consOp x , (consArgs x l , Eq.refl)
nodeCover .disjoint o o' ne m ((ms , e) , (ms' , e')) =
  Empty.rec (ne (Eq.pathToEq same))
  where
  same : o ≡ o'
  same = sym (clsC-node o ms)
       ∙ cong clsC (Eq.eqToPath e ∙ sym (Eq.eqToPath e'))
       ∙ clsC-node o' ms'
