{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- "This bag contains `y`", the second client, and the one that is about
   BAGS rather than about representatives.

   `Sorted` is what the chosen head buys and `Occurs` is what it does not
   cost.  The two are the same size and have the same shape -- index,
   `look`, one recursive call at the tail -- and they differ in exactly one
   place: `Sorted`'s side condition compares the head against the INDEX, so
   it reads the order in which the elements were chosen, and `Occurs`'s
   compares the head against a fixed element, so it does not.  That single
   difference is the whole of `Chosen/Quotient`: `Occurs` descends along
   the quotient map and `Sorted` does not.

   Two departures from `Sorted`, both forced.

   The nil rule is a REFUTATION, and `nilOp` is nullary, so there is no
   slot to carry it -- gap 2, met here exactly as `Match/Judgment` meets it
   at `vtrueOp`.  `clash` builds the answer at `⊥Ty` and relabels by
   `Ans-map&`, whose hypothesis -- "this bag is a node of `nilOp`" -- is
   precisely the knowledge that makes `Occurs y` empty; and the empty
   answer enters through `none`, so convention 5 holds.

   The cons rule is a DISJUNCTION -- the head is `y`, or `y` is in the
   tail -- so its cell is `⊕Set` and not `&Set`, and the side condition
   enters by `_<|>_` rather than by `Ans-&&`.  Convention 4 says a side
   condition rides at the node rather than at a slot; it does not say which
   connective, and an alternative is not a conjunct.  This is also why the
   three answers genuinely disagree here and only nominally disagree in
   `Sorted`: `Occurs y` is NOT a proposition -- a bag with `y` in it twice
   has two derivations -- so `ND` returns the MULTIPLICITY of `y`, while
   `Dec` returns a bit and `Maybe` commits to the leftmost occurrence.  The
   multiplicity is a bag invariant; see `Chosen/Quotient`.

   Nothing below mentions `Dec`, `Maybe` or `ND`. -}
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

-- The judgment, by recursion on the model.  Proof-RELEVANT, and
-- deliberately: a derivation is an occurrence, so counting derivations
-- counts occurrences.  This is convention 7 without the indices.
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

-- The one side condition: the head is the element being looked for.  It
-- sits at the node -- there is no second slot for it -- but joined by
-- `⊕Set`, since the rule is an alternative and not a premise.
HitSet : (x y : El) → TheorySet ℓ-zero bag
HitSet x y = (λ _ → x ≡ y) , λ _ → isProp→isSet (isSetEl x y)

module _ (discEl : Discrete El) where

  decHit : (x y : El) → Decidable (ty (HitSet x y))
  decHit x y m _ = onDec (discEl x y)
    where
    onDec : Dec (x ≡ y) → DecTy (ty (HitSet x y)) m
    onDec (yes p) = Sum.inl p
    onDec (no ¬p) = Sum.inr λ p → Empty.rec (¬p p)

-- The premises: one recursive call, at the tail, for the same element.
Slots : (x y : El) → NodeArgs ℓ-zero (consOp x)
Slots x y ms theRest = OccursSet y

Cell : (x y : El) → TheorySet ℓ-zero bag
Cell x y = HitSet x y ⊕Set ⊗ᴰSet (consOp x) (Slots x y)

-- One level of unfolding, both ways, as `⊢`-terms.  Both need the cell:
-- the left summand says nothing about the head, so `roll` cannot learn the
-- shape of `m` from it.
rollNode : (x y : El) → ty (Cell x y) & NodeAt (consOp x) ⊢ Occurs y
rollNode x y m (Sum.inl p , (ms , Eq.refl)) = Sum.inl p
rollNode x y m (Sum.inr (ms , Eq.refl , ws) , _) = Sum.inr (ws theRest)

unrollNode : (x y : El) → Occurs y & NodeAt (consOp x) ⊢ ty (Cell x y)
unrollNode x y m (d , (ms , Eq.refl)) =
  Sum.rec Sum.inl
    (λ o → Sum.inr (node-mk {As = Slots x y} {ms = ms} λ where theRest → o)) d


-- The checker, for whatever answer.
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
