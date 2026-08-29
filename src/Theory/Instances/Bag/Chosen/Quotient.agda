{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- What the repair costs, as two theorems about the same quotient map.

   `toBag` is the map from the chosen-head theory to the real one: it is
   the unique homomorphism sending `x ∷ l` to `⌈gen x ⌉ ⊙ᵖ toBag l`, and
   `toBag-swap` is the one fact that makes it a map OUT of a quotient
   rather than an isomorphism -- two representatives that differ by a
   transposition have the same image.  Everything a client over
   `Chosen/Guard` decides is a predicate on the SOURCE of that map, and the
   question this module answers is which of those predicates are pullbacks
   of predicates on the target.

   `Descends A` is the obligation, spelled out: a `P` on bags and maps both
   ways over `toBag`.  It is deliberately stated as a bare logical
   equivalence rather than an equivalence of types -- weakening it makes
   the negative result stronger and the positive one honest.

   THE NEGATIVE.  `¬descendsSorted`: no `P` whatsoever induces `Sorted`.
   Not "the obvious `P` fails", not "`P` is hard to construct" -- there is
   none, and the proof is three lines, because `toBag-swap` carries the
   witness across and the other representative has no derivation.  So the
   `Sorted` client is a decision procedure about LISTS wearing the word
   bag, and no amount of care at the call site recovers a statement about
   bags from it.

   THE POSITIVE.  `descendsOccurs`: membership does descend, and the `P`
   is a fold -- `bagAny`, which is `Bags/Order`'s `bagAll` with `⊓`
   replaced by `⊔`.  The fold is the whole proof: `(ℕ, +, 0)`, `(hProp, ⊓,
   ⊤)` and `(hProp, ⊔, ⊥)` are commutative monoids, hence models of
   `BagEqns`, hence functions on bags, and a client whose judgment IS such
   a fold transports for free.  That is the general rule, and it is the
   only general rule available: a predicate on representatives descends
   when it is a homomorphism out of the free ALGEBRA, and syntax-direction
   -- which is what the framework provides -- is not that.

   The truncation in `descendsOccurs` is an artefact of choosing `⊔` and
   not of the quotient: multiplicity is a bag invariant too, so the
   untruncated `Occurs z l ≃ Fin (mult z (toBag l))` is also true, by the
   fold into `(ℕ, +, 0)` instead.  What is NOT recoverable is the
   derivation's shape -- which occurrence -- and that is `Bags/Generation`
   in one sentence: on the quotient the choice of head generator is
   truncated, because `comm` identifies the two decompositions.  That
   truncation and `Bag/Failure`'s `¬preciseNode` are the same fact seen
   from the two sides; `Precise` is exactly the untruncated uniqueness that
   `Generation` has to throw away. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Algebra.Theory.Finitary
import Cubical.Algebra.Theory.Finitary.Free.Closing as Cl
import Cubical.Data.Equality as Eq
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open SortedSig
open SortedEqns
module Theory.Instances.Bag.Chosen.Quotient
  (El : Type ℓ-zero) (isSetEl : isSet El) (le : El → El → Bool) where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Maybe using (Maybe ; nothing ; just)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.HITs.PropositionalTruncation as PT
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Relation.Nullary.Base using (¬_)
import Cubical.Data.Sum as Sum
import Cubical.Functions.Logic as L

open import Theory.Instances.Monoid.Base using (Sorts ; MonSig ; MonOp
  ; ε· ; _⊙_ ; MonEqn ; assoc ; unitL ; unitR)
open import Theory.Instances.Bags.Base El
  using (Bag ; BagEqns ; CommEqn ; comm ; mon ; ext
        ; _⊙ᵖ_ ; εᵖ ; ⌈gen_⌉ ; ⊙-comm ; ⊙-assoc ; ⊙-unitR)

import Theory.Instances.Bag.Chosen.Sorted El isSetEl le as S
import Theory.Instances.Bag.Chosen.Occurs El isSetEl as O

private variable ℓ : Level

-- The quotient map.
toBag : List El → Bag
toBag [] = εᵖ
toBag (x ∷ l) = ⌈gen x ⌉ ⊙ᵖ toBag l

-- ...and the only thing about it that matters: it does not see the order.
-- One transposition generates the rest, so this is the whole of what a
-- predicate on representatives has to be blind to.
toBag-swap : (x y : El) (l : List El)
  → toBag (x ∷ y ∷ l) ≡ toBag (y ∷ x ∷ l)
toBag-swap x y l =
    sym (⊙-assoc ⌈gen x ⌉ ⌈gen y ⌉ (toBag l))
  ∙ cong (_⊙ᵖ toBag l) (⊙-comm ⌈gen x ⌉ ⌈gen y ⌉)
  ∙ ⊙-assoc ⌈gen y ⌉ ⌈gen x ⌉ (toBag l)

-- The obligation a client owes if its verdict is to be about bags.
Descends : (List El → Type ℓ) → Type (ℓ-suc ℓ)
Descends {ℓ = ℓ} A =
  Σ[ P ∈ (Bag → Type ℓ) ]
    (((l : List El) → A l → P (toBag l))
     × ((l : List El) → P (toBag l) → A l))


-- THE NEGATIVE.  Sortedness is not a property of a bag, and the proof
-- needs only one strictly ordered pair.
module _ (x y : El) (below : le x y Eq.≡ true) (above : le y x Eq.≡ false)
  where

  private
    lo : List El
    lo = x ∷ y ∷ []

    hi : List El
    hi = y ∷ x ∷ []

    sortedLo : S.Sorted nothing lo
    sortedLo = tt , (below , tt)

    ¬sortedHi : ¬ S.Sorted nothing hi
    ¬sortedHi (_ , (q , _)) =
      true≢false (sym (Eq.eqToPath q) ∙ Eq.eqToPath above)

  ¬descendsSorted : ¬ Descends (S.Sorted nothing)
  ¬descendsSorted (P , (into , out)) =
    ¬sortedHi (out hi (subst P (toBag-swap x y []) (into lo sortedLo)))


-- THE POSITIVE.  `bagAny` is `Bags/Order`'s `bagAll` with `⊓` replaced by
-- `⊔`: still a fold, since `(hProp , ⊔ , ⊥)` is a commutative monoid, so
-- still a function on bags.
private
  Ω : Sorts → Type (ℓ-suc ℓ-zero)
  Ω _ = hProp ℓ-zero

  ⊔Ops : Ops {σ = MonSig} Ω
  ⊔Ops ε· f = L.⊥
  ⊔Ops _⊙_ f = L._⊔_ (f zero) (f (suc zero))

  ⊔Sat : (e : BagEqns .eqns)
         (ρ : (w : vars BagEqns e) → Ω (BagEqns .varSort e w))
       → TmRec Ω ⊔Ops ρ (BagEqns .lhs e) ≡ TmRec Ω ⊔Ops ρ (BagEqns .rhs e)
  ⊔Sat (mon assoc) ρ =
    sym (L.⊔-assoc (ρ zero) (ρ (suc zero)) (ρ (suc (suc zero))))
  ⊔Sat (mon unitL) ρ = L.⊔-identityˡ (ρ zero)
  ⊔Sat (mon unitR) ρ = L.⊔-identityʳ (ρ zero)
  ⊔Sat (ext comm) ρ = L.⊔-comm (ρ zero) (ρ (suc zero))

  memP : El → El → hProp ℓ-zero
  memP z w = (w ≡ z) , isSetEl w z

bagAny : (El → hProp ℓ-zero) → Bag → hProp ℓ-zero
bagAny p m = Cl.rec BagEqns (λ _ → isSetHProp) ⊔Ops ⊔Sat p m

-- "`z` is in this bag", as a predicate on bags.  `⊥` at `ε`, a join at
-- `⊙`, and `memP z` at a generator -- all on the nose, since `Cl.rec`
-- reduces at `var` and at `node`.
Mem : El → Bag → hProp ℓ-zero
Mem z = bagAny (memP z)

private
  into : (z : El) (l : List El) → O.Occurs z l → ⟨ Mem z (toBag l) ⟩
  into z (x ∷ l) (Sum.inl p) = L.inl p
  into z (x ∷ l) (Sum.inr o) = L.inr (into z l o)

  out : (z : El) (l : List El) → ⟨ Mem z (toBag l) ⟩ → ∥ O.Occurs z l ∥₁
  out z (x ∷ l) h =
    L.⊔-elim (memP z x) (Mem z (toBag l))
      (λ _ → ∥ O.Occurs z (x ∷ l) ∥₁ , squash₁)
      (λ p → ∣ Sum.inl p ∣₁)
      (λ q → PT.map Sum.inr (out z l q))
      h

-- ...and the descent.  The truncation is `⊔`'s doing and not the
-- quotient's -- see the header -- but the DIRECTION is the point: a
-- judgment that is a fold transports, and one that reads its index against
-- the order does not.
descendsOccurs : (z : El) → Descends (λ l → ∥ O.Occurs z l ∥₁)
descendsOccurs z =
    (λ m → ⟨ Mem z m ⟩)
  , ( (λ l → PT.rec (Mem z (toBag l) .snd) (into z l))
    , out z )
