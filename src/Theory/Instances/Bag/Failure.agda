{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- GAP 4, made into three refutations.

   `Theory/Combinator/README`'s fourth gap says that `Precise` is what
   replaced "the alphabet is discrete", and that a quotiented theory does
   not have it.  That is an assertion about the framework, so it can be
   *proved*, and this module proves it at the smallest instance that
   exhibits the phenomenon: bags over `Bool`, which is
   `Theory/Instances/Bags/Base` at a two-element carrier.

   Three statements, in increasing order of how much they cost the
   framework.

   1.  `¬ preciseNode` -- `Precise _⊙_` is FALSE.  The bag `{true,false}`
       is `{true} ⊙ {false}` and it is `{false} ⊙ {true}`, and those two
       decompositions differ in their first slot, so `NodeAt _⊙_` is not a
       proposition.  `Ans-node` demands `Precise o` as a hypothesis, so no
       client over this theory can ever invoke the node rule at `_⊙_` --
       which is to say, no client over this theory can ever do syntax-
       directed case analysis on a bag.  This is the whole of gap 4.

   2.  `¬ disjointNode` -- the node cover by head operation is not
       disjoint, because `ε` is a node of `ε·` and a node of `_⊙_`.  This
       one is worth stating and worth *discounting*: it is not the
       commutativity failure.  The free monoid has it too -- `[] = [] ++
       []` -- which is why `Theory/Instances/Monoid` covers strings by
       LOOKAHEAD and not by head operation.  Any theory whose signature has
       a unit equation loses this cover, commutative or not.

   3.  `¬ disjointHead` -- and neither does the repair that suggests
       itself.  `Bags/Order` already imposes a decidable order on `El`, so
       the obvious move is to cover the bags by which generator sits at the
       front: `Head y` is "`m` is `y` together with something".  That is
       the cover the README is describing when it says `{a,b}` is a node of
       two different heads, and it fails for exactly that reason -- the
       bag `{true,false}` is `true` on the front of `{false}` AND `false`
       on the front of `{true}`.  A boolean `le` does not help: no
       predicate on bags can pick the front of a bag out, because being at
       the front is not a property the bag has.

   What survives is `preciseUnit`: the NULLARY operation is precise, since
   its slot tuple is unique by `funExt λ ()` and the equation is a
   proposition.  A commutative theory keeps precision exactly at the
   operations that have no room to permute anything.  That is not a
   consolation -- it means the only node rule available is the one with no
   premises.

   The separating invariant is `count`, a fold into `(ℕ , + , 0)`, which is
   a commutative monoid and so a model of `BagEqns`.  It is the same shape
   as `Bags/Rank`'s `size`, with `λ _ → 1` replaced by a weight that
   distinguishes the two generators; `Cl.rec` reduces on `gen` and on
   `node`, so `count ⌈gen b ⌉` is `weight b` on the nose and the
   separation is `snotz`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Algebra.Theory.Finitary.Free.Closing as Cl
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns
module Theory.Instances.Bag.Failure where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Empty using (⊥)
import Cubical.Data.Empty as Empty
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; isSetℕ ; +-assoc
  ; +-comm ; +-zero ; snotz)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd ; ΣPathP)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)
open import Cubical.Relation.Nullary.Base using (¬_)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Bags.Base Bool
open import Theory.Type.Top.Base BagEqns Bool (λ _ → tt) closingPresentation
open import Theory.Type.Bottom.Base BagEqns Bool (λ _ → tt) closingPresentation
open import Theory.Type.Product.Binary.Base
  BagEqns Bool (λ _ → tt) closingPresentation
open import Theory.Type.Cover.Base BagEqns Bool (λ _ → tt) closingPresentation
open import Theory.Combinator.Core BagEqns Bool (λ _ → tt) closingPresentation


-- The separating invariant: a fold into `(ℕ , + , 0)`, which satisfies
-- every equation of `BagEqns` -- the three monoid ones and commutativity.
private
  N : Sorts → Type ℓ-zero
  N _ = ℕ

  +Ops : Ops {σ = MonSig} N
  +Ops ε· f = zero
  +Ops _⊙_ f = f zero + f (suc zero)

  +Sat : (e : BagEqns .eqns)
         (ρ : (w : vars BagEqns e) → N (BagEqns .varSort e w))
       → TmRec N +Ops ρ (BagEqns .lhs e) ≡ TmRec N +Ops ρ (BagEqns .rhs e)
  +Sat (mon assoc) ρ = sym (+-assoc (ρ zero) (ρ (suc zero)) (ρ (suc (suc zero))))
  +Sat (mon unitL) ρ = refl
  +Sat (mon unitR) ρ = +-zero (ρ zero)
  +Sat (ext comm) ρ = +-comm (ρ zero) (ρ (suc zero))

  weight : Bool → ℕ
  weight true = 1
  weight false = 0

count : Bag → ℕ
count m = Cl.rec BagEqns (λ _ → isSetℕ) +Ops +Sat weight m

-- ...and what it separates.  `Cl.rec` computes at a generator, so both
-- sides reduce and the whole proof is `snotz`.
genDistinct : ¬ (⌈gen true ⌉ ≡ ⌈gen false ⌉)
genDistinct p = snotz (cong count p)


-- Named slots, and the one bag that everything below is stated at:
-- `{true,false}`, decomposed the two ways commutativity makes available.
-- The tuples are `two`, not a bespoke function: `_⊙ᵖ_` is `op _⊙_ ∘ two`,
-- and a decomposition has to be the tuple the carrier operation used.
pattern theL = zero
pattern theR = suc zero

mix : Bag
mix = ⌈gen true ⌉ ⊙ᵖ ⌈gen false ⌉

leftFirst rightFirst : NodeAt _⊙_ mix
leftFirst = two ⌈gen true ⌉ ⌈gen false ⌉ , Eq.refl
rightFirst =
  two ⌈gen false ⌉ ⌈gen true ⌉
  , Eq.pathToEq (⊙-comm ⌈gen false ⌉ ⌈gen true ⌉)


-- 1.  THE NODE IS NOT PRECISE.  `Ans-node` is unavailable at `_⊙_`, and
-- with it every syntax-directed rule this framework has.
¬preciseNode : ¬ (Precise _⊙_)
¬preciseNode prec =
  genDistinct (cong (λ n → n .fst theL) (prec mix leftFirst rightFirst))

-- The nullary operation keeps its precision -- there is nothing to permute
-- when there is nothing to permute.  This is the whole of what survives.
preciseUnit : Precise ε·
preciseUnit m (ms , e) (ms' , e') =
  ΣPathP (funExt (λ ()) , isProp→PathP (λ _ → isPropModelEq) e e')


-- 2.  THE NODE COVER IS NOT DISJOINT -- but for the unit equation, not for
-- commutativity.  The free monoid fails this too.
unitNode : NodeAt ε· εᵖ
unitNode = (λ ()) , Eq.refl

unitSplit : NodeAt _⊙_ εᵖ
unitSplit = two εᵖ εᵖ , Eq.pathToEq (⊙-unitL εᵖ)

¬disjointNode : ¬ (Disjoint NodeAt)
¬disjointNode dis with dis ε· _⊙_ (λ ()) εᵖ (unitNode , unitSplit)
... | ()


-- 3.  AND NEITHER IS THE COVER BY CHOSEN HEAD.  `Head y` is "`m` is `y`
-- with something after it", the cover a decidable order on `El` is
-- supposed to make usable; `{true,false}` is in two of its cells.
Head : Bool → TheoryTy ℓM tt
Head y = ⌈ ⌈gen y ⌉ ⌉ ⊎B ⊤Ty

trueHead : Head true mix
trueHead = two ⌈gen true ⌉ ⌈gen false ⌉ , Eq.refl , (Eq.refl , tt , tt*)

falseHead : Head false mix
falseHead =
  two ⌈gen false ⌉ ⌈gen true ⌉
  , Eq.pathToEq (⊙-comm ⌈gen false ⌉ ⌈gen true ⌉)
  , (Eq.refl , tt , tt*)

¬disjointHead : ¬ (Disjoint Head)
¬disjointHead dis with dis true false (λ ()) mix (trueHead , falseHead)
... | ()
