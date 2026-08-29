{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- What the generic combinators ask of the value theory: precision of every
   operation, a well-founded order for the guard, and a cover by head
   constructor.

   Same shape as `Instances/Annotated/Guard`, and shorter, because `VOp` is
   *finite*: there is no external annotation on an operation, so the node
   cover has three cells and a branch may be written by listing them.  That
   finiteness is also what makes `Exhaustive` possible -- a cover of the
   value type by three clauses is a statement one can write down, where a
   cover of the annotated terms by `AOp` is not.

   The one thing precision has to work around here is arity zero.
   `NodeAt vtrueOp m` is `Σ (vs : Fin 0 → Val) (vtrue ≡ m)`; the slot tuple
   is unique by `funExt λ ()` rather than by projecting a constructor, so
   the nullary cases of `preciseV` are the *easy* ones and the pair is the
   one that needs `pairFst`/`pairSnd`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Type.Later.Indexed as LI
module Theory.Instances.Match.Guard where

open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-comm ; +-suc)
import Cubical.Data.Nat.Order as NO
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Sigma using (ΣPathP ; _,_ ; fst ; snd)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Match.Base public
open import Theory.Base VEqns NoVar noVarSort vPresentation public
  hiding (Val)
open import Theory.Type.HLevels VEqns NoVar noVarSort vPresentation public
open import Theory.Type.Top.Base VEqns NoVar noVarSort vPresentation public
open import Theory.Type.Bottom.Base VEqns NoVar noVarSort vPresentation public
open import Theory.Type.Sum.Base VEqns NoVar noVarSort vPresentation public
open import Theory.Type.Sum.Binary.Base
  VEqns NoVar noVarSort vPresentation public
open import Theory.Type.Product.Binary.Base
  VEqns NoVar noVarSort vPresentation public
open import Theory.Type.Cover.Base VEqns NoVar noVarSort vPresentation public
open import Theory.Type.Decidable.Base
  VEqns NoVar noVarSort vPresentation public
open import Theory.Combinator.Core VEqns NoVar noVarSort vPresentation public

private variable ℓX : Level

-- Names for the argument positions of `vpairOp`.  The nullary operations
-- have none, which is exactly why they need `Judgment`'s `clashAt`.
pattern theFst = zero
pattern theSnd = suc zero

-- Constructor injectivity, by projection rather than by matching `Eq.refl`.
pairFst pairSnd : Val → Val
pairFst vtrue = vtrue
pairFst vfalse = vfalse
pairFst (vpair v _) = v
pairSnd vtrue = vtrue
pairSnd vfalse = vfalse
pairSnd (vpair _ w) = w

preciseV : (o : VOp) → Precise o
preciseV vtrueOp m (vs , e) (vs' , e') =
  ΣPathP (funExt (λ ()) , isProp→PathP (λ _ → isPropModelEq) e e')
preciseV vfalseOp m (vs , e) (vs' , e') =
  ΣPathP (funExt (λ ()) , isProp→PathP (λ _ → isPropModelEq) e e')
preciseV vpairOp m (vs , e) (vs' , e') =
  ΣPathP (funExt slot , isProp→PathP (λ _ → isPropModelEq) e e')
  where
  whole : vpair (vs theFst) (vs theSnd) ≡ vpair (vs' theFst) (vs' theSnd)
  whole = Eq.eqToPath e ∙ sym (Eq.eqToPath e')

  slot : (a : Fin 2) → vs a ≡ vs' a
  slot theFst = cong pairFst whole
  slot theSnd = cong pairSnd whole

-- The measure.
vSize : Val → ℕ
vSize vtrue = 1
vSize vfalse = 1
vSize (vpair v w) = suc (vSize v + vSize w)

private
  fst< : (v w : Val) → vSize v NO.< vSize (vpair v w)
  fst< v w = vSize w , (+-suc (vSize w) (vSize v)
    ∙ cong suc (+-comm (vSize w) (vSize v)))

  snd< : (v w : Val) → vSize w NO.< vSize (vpair v w)
  snd< v w = vSize v , +-suc (vSize v) (vSize w)

module Subvalue {X : Type ℓX} (isSetX : isSet X) (rank : X → ℕ) where

  srt : X → VSort
  srt _ = val

  order : LI.IPtOrder VEqns NoVar noVarSort vPresentation srt ℓ-zero
  order = LI.ilexOrder VEqns NoVar noVarSort vPresentation srt
    isSetX (λ _ → vSize) rank

  open LI.IPtOrder order using (_<_) public

  smaller : {x x' : X} {v v' : Val}
    → vSize v' NO.< vSize v → (x' , v') < (x , v)
  smaller lt = lift (Sum.inl lt)

  callFst : {x x' : X} (v w : Val) → (x' , v) < (x , vpair v w)
  callFst v w = smaller (fst< v w)

  callSnd : {x x' : X} (v w : Val) → (x' , w) < (x , vpair v w)
  callSnd v w = smaller (snd< v w)

-- Argument tuples.
pairArgs : Val → Val → (b : Fin 2) → ↓M (VSortOf vpairOp b)
pairArgs v w theFst = v
pairArgs v w theSnd = w

-- The node cover, by head constructor.  Three cells, and `total` is the
-- induction principle of `Val` while `disjoint` is no-confusion.
clsV : Val → VOp
clsV vtrue = vtrueOp
clsV vfalse = vfalseOp
clsV (vpair _ _) = vpairOp

clsV-node : (o : VOp) (vs : interpIn o ↓M) → clsV (op o vs) ≡ o
clsV-node vtrueOp vs = refl
clsV-node vfalseOp vs = refl
clsV-node vpairOp vs = refl

nodeCover : Cover VOp NodeAt
nodeCover .total vtrue _ = vtrueOp , ((λ ()) , Eq.refl)
nodeCover .total vfalse _ = vfalseOp , ((λ ()) , Eq.refl)
nodeCover .total (vpair v w) _ = vpairOp , (pairArgs v w , Eq.refl)
nodeCover .disjoint o o' ne m ((vs , e) , (vs' , e')) =
  Empty.rec (ne (Eq.pathToEq same))
  where
  same : o ≡ o'
  same = sym (clsV-node o vs)
       ∙ cong clsV (Eq.eqToPath e ∙ sym (Eq.eqToPath e'))
       ∙ clsV-node o' vs'
