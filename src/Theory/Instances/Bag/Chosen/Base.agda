{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- The repair: bags with a CHOSEN head, presented so that the head is part
   of the operation.

   `Bag/Failure` proves that the commutative theory has no precise binary
   operation and no disjoint node cover, so nothing over it can reach
   `Ans-node`.  `Bags/Order` suggests the fix -- impose a decidable order
   and pick a canonical head -- and the point of this module is that the
   fix cannot be made inside the theory.  `Precise o` quantifies over every
   element of the result sort, so it is a property of the SIGNATURE and no
   predicate, order or side condition added later can restore it.  The
   repair therefore changes the theory, and this is the changed theory.

   `consOp x` is unary and carries its element in the OPERATION, exactly as
   `Layout/Base`'s `consOp t` carries a token and `Annotated/Base`'s
   `appOp B` carries an annotation.  That is what makes the head a
   syntactic fact rather than a property of a quotient: the decomposition
   of `x ∷ l` along `consOp x` is `l` and nothing else.  There are no
   equations, so `Precise` and no-confusion come back for free, and the
   node cover is by head constructor, one token of lookahead, as for every
   other free client.

   And that is the cost, stated at the top rather than hidden: the free
   model of this signature is `List El`.  The sort is called `bag`, and it
   is a list.  What `Sorted` and `Occurs` decide are properties of
   REPRESENTATIVES; `Quotient` says which of them descend along `toBag` and
   which do not.

   `V` is `⊥`: a bag is built from its elements by the operations alone, so
   `gen`/`recGen` are empty, and `noVar` is named rather than written
   `λ ()` at each use, since two absurd lambdas are not definitionally
   equal and every module in the chain must be applied to the same one.

   The carrier is `Cubical.Data.List` and not a bespoke datatype -- the
   departure from `Layout/Base`, which copies `List` to keep its
   operations definitional.  Here `op (consOp x) ms` is `x ∷ ms zero` on
   the nose already, and `isOfHLevelList` supplies the `isSet` that
   `Layout` spends an indexed W-type on. -}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns
module Theory.Instances.Bag.Chosen.Base
  (El : Type ℓ-zero) (isSetEl : isSet El) where

open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.List.Properties using (isOfHLevelList)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr ; isSet⊎)
open import Cubical.Data.Unit using (Unit ; tt ; isSetUnit)
open import Cubical.Foundations.HLevels using (isOfHLevelRetract)

-- The signature: one sort, one nullary operation, one unary operation per
-- element.  No equations.
data CSort : Type ℓ-zero where
  bag : CSort

data COp : Type ℓ-zero where
  nilOp : COp
  consOp : El → COp

CAr : COp → ℕ
CAr nilOp = 0
CAr (consOp _) = 1

CSortOf : (o : COp) → Fin (CAr o) → CSort
CSortOf _ _ = bag

CSig : SortedSig CSort ℓ-zero
CSig .ops = COp
CSig .arity = CAr
CSig .sortOf = CSortOf
CSig .resultSort _ = bag

CEqns : SortedEqns CSig ℓ-zero
CEqns .eqns = ⊥
CEqns .eqnSort ()
CEqns .varCount ()
CEqns .varSort ()
CEqns .lhs ()
CEqns .rhs ()

private
  opRep : COp → Unit ⊎ El
  opRep nilOp = inl tt
  opRep (consOp x) = inr x

  opUnrep : Unit ⊎ El → COp
  opUnrep (inl _) = nilOp
  opUnrep (inr x) = consOp x

  opRet : (o : COp) → opUnrep (opRep o) ≡ o
  opRet nilOp = refl
  opRet (consOp x) = refl

isSetCOp : isSet COp
isSetCOp = isOfHLevelRetract 2 opRep opUnrep opRet (isSet⊎ isSetUnit isSetEl)

private
  srtRet : (s : CSort) → bag ≡ s
  srtRet bag = refl

isSetCSort : isSet CSort
isSetCSort = isOfHLevelRetract 2 (λ _ → tt) (λ _ → bag) srtRet isSetUnit

-- The model.  `op (consOp x) ms` is `x ∷ ms zero`, definitionally, which
-- is the whole reason the tests below reduce.
Crr : CSort → Type ℓ-zero
Crr bag = List El

isSetCrr : (s : CSort) → isSet (Crr s)
isSetCrr bag = isOfHLevelList 0 isSetEl

noVar : ⊥ → CSort
noVar ()

open import Theory.Free.Base CEqns ⊥ noVar

private
  cOps : Ops {σ = CSig} Crr
  cOps nilOp xs = []
  cOps (consOp x) xs = x ∷ xs zero

  cSat : (e : CEqns .eqns)
    (ρ : (w : vars CEqns e) → Crr (CEqns .varSort e w))
    → TmRec Crr cOps ρ (CEqns .lhs e) ≡ TmRec Crr cOps ρ (CEqns .rhs e)
  cSat () ρ

  CModel : MOD CEqns ℓ-zero .ob
  CModel = (λ s → Crr s , isSetCrr s) , cOps , cSat

module Fold {ℓX} {X : CSort → Type ℓX} (α : Ops {σ = CSig} X) where

  foldL : List El → X bag
  foldL [] = α nilOp λ ()
  foldL (x ∷ l) = α (consOp x) λ _ → foldL l

  fold : (s : CSort) → Crr s → X s
  fold bag = foldL

  foldOp : (o : COp) (ms : (a : Fin (CAr o)) → Crr (CSortOf o a))
    → fold bag (cOps o ms) ≡ α o (λ a → fold (CSortOf o a) (ms a))
  foldOp nilOp ms = cong (α nilOp) (funExt λ ())
  foldOp (consOp x) ms = cong (α (consOp x)) (funExt λ where zero → refl)

  module _ (f : (s : CSort) → Crr s → X s)
    (homf : (o : COp) (ms : (a : Fin (CAr o)) → Crr (CSortOf o a))
          → f bag (cOps o ms) ≡ α o (λ a → f (CSortOf o a) (ms a))) where

    foldUniqL : (l : List El) → f bag l ≡ foldL l
    foldUniqL [] = homf nilOp (λ ()) ∙ cong (α nilOp) (funExt λ ())
    foldUniqL (x ∷ l) =
        homf (consOp x) (λ _ → l)
      ∙ cong (α (consOp x)) (funExt λ where zero → foldUniqL l)

    foldUniq : (s : CSort) (m : Crr s) → f s m ≡ fold s m
    foldUniq bag = foldUniqL

cPresentation : FreePresentation ℓ-zero
cPresentation .P = CModel
cPresentation .satStrict () ρ
cPresentation .gen ()
cPresentation .rec {X = X} isSetX α sat ρ {s} = Fold.fold {X = X} α s
cPresentation .recGen isSetX α sat ρ ()
cPresentation .recOp {X = X} isSetX α sat ρ = Fold.foldOp {X = X} α
cPresentation .recUniq {X = X} isSetX α sat ρ f homf fβ {s} =
  Fold.foldUniq {X = X} α f homf s
