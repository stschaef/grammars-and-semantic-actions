{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Sortedness, indexed by a lower bound (`nothing` is -∞).  The side condition
   `b ≤ x` compares the index with the operation's own element, so it rides on
   the NODE, not a slot.  Not a statement about bags: see `Chosen/Quotient`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Theory.Finitary
open import Cubical.Data.Bool
  using (Bool ; true ; false ; isSetBool ; true≢false)
open SortedSig
open SortedEqns
module Theory.Instances.Bag.Chosen.Sorted
  (El : Type ℓ-zero) (isSetEl : isSet El) (le : El → El → Bool) where

open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Maybe using (Maybe ; nothing ; just)
open import Cubical.Data.Maybe.Properties using (isOfHLevelMaybe)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt ; isPropUnit)
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Bag.Chosen.Guard El isSetEl public

Bnd : Type ℓ-zero
Bnd = Maybe El

isSetBnd : isSet Bnd
isSetBnd = isOfHLevelMaybe 0 isSetEl

private
  isPropBoolEq : {b c : Bool} → isProp (b Eq.≡ c)
  isPropBoolEq =
    isOfHLevelRetractFromIso 1 (invIso Eq.PathIsoEq) (isSetBool _ _)

GeT : Bnd → El → Type ℓ-zero
GeT nothing x = Unit
GeT (just y) x = le y x Eq.≡ true

isPropGeT : (b : Bnd) (x : El) → isProp (GeT b x)
isPropGeT nothing x = isPropUnit
isPropGeT (just y) x = isPropBoolEq

decGeT : (b : Bnd) (x : El) → Dec (GeT b x)
decGeT nothing x = yes tt
decGeT (just y) x = onLe (le y x) Eq.refl
  where
  onLe : (v : Bool) → le y x Eq.≡ v → Dec (le y x Eq.≡ true)
  onLe true p = yes p
  onLe false p =
    no λ q → true≢false (sym (Eq.eqToPath q) ∙ Eq.eqToPath p)

Sorted : Bnd → TheoryTy ℓ-zero bag
Sorted b [] = Unit
Sorted b (x ∷ l) = GeT b x × Sorted (just x) l

isPropSorted : (b : Bnd) (l : List El) → isProp (Sorted b l)
isPropSorted b [] = isPropUnit
isPropSorted b (x ∷ l) = isProp× (isPropGeT b x) (isPropSorted (just x) l)

SortedSet : Bnd → TheorySet ℓ-zero bag
SortedSet b = Sorted b , λ l → isProp→isSet (isPropSorted b l)

SideT : (o : COp) → Bnd → Type ℓ-zero
SideT nilOp b = Unit
SideT (consOp x) b = GeT b x

isPropSideT : (o : COp) (b : Bnd) → isProp (SideT o b)
isPropSideT nilOp b = isPropUnit
isPropSideT (consOp x) b = isPropGeT b x

decSideT : (o : COp) (b : Bnd) → Dec (SideT o b)
decSideT nilOp b = yes tt
decSideT (consOp x) b = decGeT b x

SideSet : (o : COp) → Bnd → TheorySet ℓ-zero bag
SideSet o b = (λ _ → SideT o b) , λ _ → isProp→isSet (isPropSideT o b)

decSide : (o : COp) (b : Bnd) → Decidable (ty (SideSet o b))
decSide o b m _ = onDec (decSideT o b)
  where
  onDec : Dec (SideT o b) → DecTy (ty (SideSet o b)) m
  onDec (yes w) = Sum.inl w
  onDec (no ¬w) = Sum.inr λ w → Empty.rec (¬w w)

Slots : (o : COp) → Bnd → NodeArgs ℓ-zero o
Slots nilOp b ms ()
Slots (consOp x) b ms theRest = SortedSet (just x)

Cell : (o : COp) → Bnd → TheorySet ℓ-zero bag
Cell o b = ⊗ᴰSet o (Slots o b) &Set SideSet o b

rollNode : (o : COp) (b : Bnd) → ty (Cell o b) ⊢ Sorted b
rollNode nilOp b m ((ms , Eq.refl , ws) , sd) = tt
rollNode (consOp x) b m ((ms , Eq.refl , ws) , sd) = sd , ws theRest

unrollNode : (o : COp) (b : Bnd) → Sorted b & NodeAt o ⊢ ty (Cell o b)
unrollNode nilOp b m (d , (ms , Eq.refl)) = node-mk {ms = ms} (λ ()) , tt
unrollNode (consOp x) b m (d , (ms , Eq.refl)) =
  node-mk {ms = ms} (λ where theRest → d .snd) , d .fst


module Check (𝒯 : AnswerFunctor) where

  open Subbag {X = Bnd} isSetBnd (λ _ → 0) hiding (_<_) public
  open Combinators 𝒯 srt order public

  step : Step SortedSet
  step b = look nodeCover branch
    where
    nodeAns : (o : COp) → ▷ (AnsFam SortedSet) b & NodeAt o
      ⊢ ty (Ans (⊗ᴰSet o (Slots o b)))
    nodeAns nilOp m (β , (ms , Eq.refl)) =
      Ans-node nilOp (preciseC nilOp) {As = Slots nilOp b} {ms = ms} λ ()
    nodeAns (consOp x) m (β , (ms , Eq.refl)) =
      Ans-node (consOp x) (preciseC (consOp x))
        {As = Slots (consOp x) b} {ms = ms}
        λ where
          theRest → callAt (just x)
            (callRest {i = b} {i' = just x} x (ms theRest)) β

    cellAns : (o : COp) → ▷ (AnsFam SortedSet) b & NodeAt o
      ⊢ ty (Ans (Cell o b))
    cellAns o = Ans-&& ∘⊢ (nodeAns o ,& side (decSide o b))

    branch : (o : COp) → ▷ (AnsFam SortedSet) b & NodeAt o
      ⊢ ty (Ans (SortedSet b))
    branch o =
      Ans-map& (rollNode o b ∘⊢ π₁) (unrollNode o b) ∘⊢ (cellAns o ,& π₂)

  inOrder : Checker SortedSet
  inOrder = fix step
