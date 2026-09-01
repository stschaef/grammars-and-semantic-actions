{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- "This bag contains `y`": about BAGS, not representatives — `Occurs` compares the head
   against a fixed element, not the index (that is the whole of `Chosen/Quotient`).
   The nil rule is a refutation with no slot to carry it; the cons rule is a disjunction,
   so its cell is `⊕Set` and the side condition enters by `_<|>_`, not `Ans-&&`.
   `Occurs y` is NOT a prop: `ND` returns multiplicity, `Dec` a bit, `Maybe` the leftmost. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Bag.Chosen.Occurs
  (El : Type ℓ-zero) (isSetEl : isSet El) where

open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Sum using (_⊎_ ; isSet⊎)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no ; Discrete)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Bag.Chosen.Guard El isSetEl public

-- proof-RELEVANT deliberately: a derivation is an occurrence (convention 7 without indices)
Occurs : El → TheoryTy ℓ-zero bag
Occurs y [] = ⊥
Occurs y (x ∷ l) = (x ≡ y) ⊎ Occurs y l

isSetOccurs : (y : El) (l : List El) → isSet (Occurs y l)
isSetOccurs y [] = isProp→isSet Empty.isProp⊥
isSetOccurs y (x ∷ l) =
  isSet⊎ (isProp→isSet (isSetEl x y)) (isSetOccurs y l)

OccursSet : El → TheorySet ℓ-zero bag
OccursSet y = Occurs y , isSetOccurs y

⊥Set : TheorySet ℓ-zero bag
⊥Set = ⊥Ty , isSet⊥Ty

-- sits at the node, joined by `⊕Set`: an alternative, not a premise
HitSet : (x y : El) → TheorySet ℓ-zero bag
HitSet x y = (λ _ → x ≡ y) , λ _ → isProp→isSet (isSetEl x y)

module _ (discEl : Discrete El) where

  decHit : (x y : El) → Decidable (ty (HitSet x y))
  decHit x y m _ = onDec (discEl x y)
    where
    onDec : Dec (x ≡ y) → DecTy (ty (HitSet x y)) m
    onDec (yes p) = Sum.inl p
    onDec (no ¬p) = Sum.inr λ p → Empty.rec (¬p p)

Slots : (x y : El) → NodeArgs ℓ-zero (consOp x)
Slots x y ms theRest = OccursSet y

Cell : (x y : El) → TheorySet ℓ-zero bag
Cell x y = HitSet x y ⊕Set ⊗ᴰSet (consOp x) (Slots x y)

-- both need the cell: the left summand says nothing about the head, so `roll`
-- cannot learn the shape of `m` from it
rollNode : (x y : El) → ty (Cell x y) & NodeAt (consOp x) ⊢ Occurs y
rollNode x y m (Sum.inl p , (ms , Eq.refl)) = Sum.inl p
rollNode x y m (Sum.inr (ms , Eq.refl , ws) , _) = Sum.inr (ws theRest)

unrollNode : (x y : El) → Occurs y & NodeAt (consOp x) ⊢ ty (Cell x y)
unrollNode x y m (d , (ms , Eq.refl)) =
  Sum.rec Sum.inl
    (λ o → Sum.inr (node-mk {As = Slots x y} {ms = ms} λ where theRest → o)) d


module Check (discEl : Discrete El) (𝒯 : AnswerFunctor) where

  open Subbag {X = El} isSetEl (λ _ → 0) hiding (_<_) public
  open Combinators 𝒯 srt order public

  step : Step OccursSet
  step y = look nodeCover branch
    where
    -- the empty bag: a refutation with no slot to ride in
    clash : ▷ (AnsFam OccursSet) y & NodeAt nilOp ⊢ ty (Ans (OccursSet y))
    clash =
      Ans-map& (λ _ (b , _) → Empty.rec* b)
               (λ where _ (d , (ms , Eq.refl)) → Empty.rec d)
      ∘⊢ (none {A = ⊥Set} (λ _ _ b → b) ,& π₂)

    nodeAns : (x : El) → ▷ (AnsFam OccursSet) y & NodeAt (consOp x)
      ⊢ ty (Ans (⊗ᴰSet (consOp x) (Slots x y)))
    nodeAns x m (β , (ms , Eq.refl)) =
      Ans-node (consOp x) (preciseC (consOp x))
        {As = Slots x y} {ms = ms}
        λ where
          theRest → callAt y (callRest {i = y} {i' = y} x (ms theRest)) β

    cellAns : (x : El) → ▷ (AnsFam OccursSet) y & NodeAt (consOp x)
      ⊢ ty (Ans (Cell x y))
    cellAns x = side (decHit discEl x y) <|> nodeAns x

    branch : (o : COp) → ▷ (AnsFam OccursSet) y & NodeAt o
      ⊢ ty (Ans (OccursSet y))
    branch nilOp = clash
    branch (consOp x) =
      Ans-map& (rollNode x y) (unrollNode x y) ∘⊢ (cellAns x ,& π₂)

  contains : Checker OccursSet
  contains = fix step
