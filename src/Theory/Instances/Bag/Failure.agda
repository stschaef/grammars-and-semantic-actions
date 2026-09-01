{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
-- GAP 4: quotiented theories lack `Precise`, shown at bags over `Bool`:
-- `{true,false}` decomposes two ways (`¬preciseNode`), and the unit
-- equation breaks both covers (`¬disjointNode`, `¬disjointHead`).
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


-- separating invariant: a fold into `(ℕ , + , 0)`
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

genDistinct : ¬ (⌈gen true ⌉ ≡ ⌈gen false ⌉)
genDistinct p = snotz (cong count p)


-- Decompositions must use the tuple `two`: `_⊙ᵖ_` is `op _⊙_ ∘ two`.
pattern theL = zero
pattern theR = suc zero

mix : Bag
mix = ⌈gen true ⌉ ⊙ᵖ ⌈gen false ⌉

leftFirst rightFirst : NodeAt _⊙_ mix
leftFirst = two ⌈gen true ⌉ ⌈gen false ⌉ , Eq.refl
rightFirst =
  two ⌈gen false ⌉ ⌈gen true ⌉
  , Eq.pathToEq (⊙-comm ⌈gen false ⌉ ⌈gen true ⌉)


-- 1. `_⊙_` is not precise, so `Ans-node` is unavailable at it.
¬preciseNode : ¬ (Precise _⊙_)
¬preciseNode prec =
  genDistinct (cong (λ n → n .fst theL) (prec mix leftFirst rightFirst))
-- 2. The node cover is not disjoint -- by the unit equation, not by
-- commutativity; the free monoid fails it too.
unitNode : NodeAt ε· εᵖ
unitNode = (λ ()) , Eq.refl

unitSplit : NodeAt _⊙_ εᵖ
unitSplit = two εᵖ εᵖ , Eq.pathToEq (⊙-unitL εᵖ)

¬disjointNode : ¬ (Disjoint NodeAt)
¬disjointNode dis with dis ε· _⊙_ (λ ()) εᵖ (unitNode , unitSplit)
... | ()


-- 3. The cover by chosen head is not disjoint: `{true,false}` is in the
-- `true` cell and the `false` cell.
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
