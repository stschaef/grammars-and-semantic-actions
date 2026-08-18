{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The sequencing/CPS theory of `Theory.Type.Cont.Linear`, instantiated at
   the string tensor: its coherences are discharged from `Strings` and
   `Residual`, and the letter parser is exhibited as a CPS element that
   computes. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.RecursiveDescent.Cont
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Unit using (tt ; tt*)

open import Theory.Instances.Monoid.RecursiveDescent.List Alphabet _≟_ public
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
import Theory.Type.Cont.Linear MonEqns Alphabet (λ _ → tt) listPresentation as C

private variable ℓA ℓB ℓK : Level

------------------------------------------------------------------------
-- Sequencing against a continuation, at strings.

module Sq = C.Sequencing tt (λ ℓa ℓb → ℓ-max ℓM (ℓ-max ℓa ℓb)) _⊗_ ℓM εTy
  ⊗-map ⊗-assoc ⊗-assoc⁻ ⊗-unit-l ⊗ε-unit-l⁻ ⊗ε-unit-r ⊗ε-unit-r⁻

-- The same transform with every grammar at one level: that is what makes
-- `CPS` a `Type` rather than `Typeω`, and so its laws statable.  The level
-- is a *parameter* -- `ℓ0` already was one in `SequencingU`; what pinned it
-- here was the unit, since `CPS I` forces `I` to sit at `ℓ0`.  Lifting
-- `εTy` is the whole of the repair: every other coherence at strings is
-- already level-polymorphic, and the lifted composites are definitionally
-- the unlifted ones, so their proofs transfer on the nose.
module Level⊗ᶜ (ℓ : Level) where
  private
    ℓ0 : Level
    ℓ0 = ℓ-max ℓM ℓ

    variable A K L : TheoryTy ℓ0 tt

  ε↑ : TheoryTy ℓ0 tt
  ε↑ = LiftTheoryTy ℓ εTy

  ε↑-unit-l : ε↑ ⊗ A ⊢ A
  ε↑-unit-l = ⊗-unit-l ∘⊢ (lowerG ,⊗ id⊢)

  ε↑-unit-l⁻ : A ⊢ ε↑ ⊗ A
  ε↑-unit-l⁻ = (liftG ,⊗ id⊢) ∘⊢ ⊗ε-unit-l⁻

  ε↑-unit-r : A ⊗ ε↑ ⊢ A
  ε↑-unit-r = ⊗ε-unit-r ∘⊢ (id⊢ ,⊗ lowerG)

  ε↑-unit-r⁻ : A ⊢ A ⊗ ε↑
  ε↑-unit-r⁻ = (id⊢ ,⊗ liftG) ∘⊢ ⊗ε-unit-r⁻

  module SqU = C.SequencingU tt ℓ0 _⊗_ ε↑
    ⊗-map ⊗-assoc ⊗-assoc⁻ ε↑-unit-l ε↑-unit-l⁻ ε↑-unit-r ε↑-unit-r⁻

  -- The naturalities `Strings` states at `ℓM`.  All but the left unitor's
  -- are `refl` at any level; that one is `transportEq-nat`, which is
  -- level-polymorphic already, so nothing about the level is at stake.
  ε↑-unit-l-nat : (f : K ⊢ L) → f ∘⊢ ε↑-unit-l ≡ ε↑-unit-l ∘⊢ ⊗-map id⊢ f
  ε↑-unit-l-nat f = funExt λ m → funExt λ where
    (ms , e , (u , (a , _))) →
      transportEq-nat f (Eq.pathToEq (unit-lPath ms (u .lower) e)) a

  module SqSt = SqU.Structural (λ _ _ _ _ → refl) (λ _ → refl)
    ε↑-unit-l-nat (λ _ → refl) (λ _ → refl)

  module Dᶜ = SqSt.Answers ℓ0 Decidable dec-retract dec-retract-id dec-retract-∘

  -- the four triangles and the pentagon, at the lifted unit
  module CPSLaws = Dᶜ.Laws
    ⊗-tri-l ⊗-tri-l⁻ ⊗-tri-r ⊗-tri-r⁻ ⊗-pent ⊗-pent⁻

  -- what a client whose continuations sit above `ℓM` could not do before:
  -- compose, rather than only apply `litFam` one letter at a time
  ⊗ᶜ-at-ℓ : {A B : TheoryTy ℓ0 tt} → Dᶜ.CPS A → Dᶜ.CPS B → Dᶜ.CPS (A ⊗ B)
  ⊗ᶜ-at-ℓ = Dᶜ._⊗ᶜ_

-- ...and the level the parser toolkit already used
module SqU = C.SequencingU tt ℓM _⊗_ εTy
  ⊗-map ⊗-assoc ⊗-assoc⁻ ⊗-unit-l ⊗ε-unit-l⁻ ⊗ε-unit-r ⊗ε-unit-r⁻

module SqSt = SqU.Structural ⊗-map-∘ ⊗-unit-l⁻-nat ⊗-unit-l-nat
                               ⊗-assoc⁻-nat ⊗-assoc-nat

-- The answer predicate the parser actually uses.  `Test` is the same notion
-- with the refutation dropped, so it is not closed under retracts.
module Dᶜ = SqSt.Answers ℓM Decidable dec-retract dec-retract-id dec-retract-∘

-- The lax monoidal structure of the parser's CPS composition, with every
-- hypothesis discharged.
module CPSLaws = Dᶜ.Laws
  ⊗-tri-l ⊗-tri-l⁻ ⊗-tri-r ⊗-tri-r⁻ ⊗-pent ⊗-pent⁻

-- The three laws, as equality of families: `Decidable` is not known to be
-- a family of sets, so `CPS≡` cannot promote `≈ᶜ` to a path here.

-- `idCPS` is a left unit of `_⊗ᶜ_`
CPS-unit-l : {A : TheoryTy ℓM tt} (c : Dᶜ.CPS A)
  → Dᶜ.mapCPS ⊗-unit-l ⊗ε-unit-l⁻ (Dᶜ._⊗ᶜ_ Dᶜ.idCPS c) Dᶜ.≈ᶜ c
CPS-unit-l = CPSLaws.⊗ᶜ-unit-l

-- ...and a right unit, unconditionally: the wedge condition is now bundled
CPS-unit-r : {A : TheoryTy ℓM tt} (c : Dᶜ.CPS A)
  → Dᶜ.mapCPS ⊗ε-unit-r ⊗ε-unit-r⁻ (Dᶜ._⊗ᶜ_ c Dᶜ.idCPS) Dᶜ.≈ᶜ c
CPS-unit-r = CPSLaws.⊗ᶜ-unit-r

-- composition is associative, up to the transform's own structure map
CPS-assoc : {A B C : TheoryTy ℓM tt}
  (c : Dᶜ.CPS A) (d : Dᶜ.CPS B) (e : Dᶜ.CPS C)
  → Dᶜ.mapCPS ⊗-assoc ⊗-assoc⁻ (Dᶜ._⊗ᶜ_ (Dᶜ._⊗ᶜ_ c d) e)
    Dᶜ.≈ᶜ Dᶜ._⊗ᶜ_ c (Dᶜ._⊗ᶜ_ d e)
CPS-assoc = CPSLaws.⊗ᶜ-assoc

-- transporting an answer along the structure map, at one word
reassoc : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {K : TheoryTy ℓK tt}
  (w : ↓M tt)
  → DecAt (Sq.Then A (Sq.Then B K)) w → DecAt (Sq.Then (A ⊗ B) K) w
reassoc w = dec-map Sq.Then-⊗⁻ (¬Ty-map Sq.Then-⊗) w

------------------------------------------------------------------------
-- Where the transform is already visible in the combinators.

-- A parser is a test of the transform at the trivial continuation; the
-- LL(1) decision below is the same transform at `FolOf x`, which is what
-- lets it refute rather than merely fail.
parser-Then : {A : TheoryTy ℓA tt} → Parser A ≡ Test (Sq.Then A ⊤Ty)
parser-Then = refl

-- `seqP`'s only generic content is `Then-⊗⁻`, and it sits *under* `p`'s
-- bind: the reassociation is fused into the first parser, not applied to
-- the composite, so `seqP` is not the lax composition on the nose.
seqP-Then : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  (p : Parser A) (q : Parser B)
  → seqP p q
    ≡ onSuccess (Monad.fmap MaybeMonad Sq.Then-⊗⁻ ∘⊢ Maybe⊗r ∘⊢ (id⊢ ,⊗ q))
      ∘⊢ p
seqP-Then p q = refl

------------------------------------------------------------------------
-- `dec-lit⊗` is the CPS element of one letter.

-- Its wedge condition says the letter parser does not inspect its
-- continuation: retracting the tail's decision before reading `c` is the
-- same as reading `c` and retracting after.  On the success branch that is
-- `refl`; the two refutations land in `⊥`.
lit-nat : {K L : TheoryTy ℓM tt} (c : Alphabet) (f : K ⊢ L) (g : L ⊢ K)
  (d : Decidable K) (w : ↓M tt)
  → dec-lit⊗ c (dec-retract f g d) w tt
    ≡ dec-retract (⊗-map id⊢ f) (⊗-map id⊢ g) (dec-lit⊗ c d) w tt
lit-nat {L = L} c f g d [] = cong Sum.inr (isProp¬Ty (＂ c ＂ ⊗ L) _ _)
lit-nat {L = L} c f g d (a ∷ as) with a ≟ c
... | Sum.inr _ = cong Sum.inr (isProp¬Ty (＂ c ＂ ⊗ L) _ _)
... | Sum.inl Eq.refl with d as tt
... | Sum.inl _ = refl
... | Sum.inr _ = cong Sum.inr (isProp¬Ty (＂ c ＂ ⊗ L) _ _)

litCPS : (c : Alphabet) → Dᶜ.CPS ＂ c ＂
litCPS c .Dᶜ.app _ δ = dec-lit⊗ c δ
litCPS c .Dᶜ.nat f g d = funExt λ w → funExt λ _ → lit-nat c f g d w

-- The same family with the continuation's level free; `CPS` fixes it at `ℓM`
-- to stay out of `Typeω`, so a client whose continuation is higher uses this.
litFam : (c : Alphabet) {K : TheoryTy ℓK tt}
  → Decidable K → Decidable (Sq.Then ＂ c ＂ K)
litFam c = dec-lit⊗ c

-- ...and at `ℓM` it *is* the CPS element's family, on the nose.
litFam-app : (c : Alphabet) (K : TheoryTy ℓM tt)
  → Dᶜ.app (litCPS c) K ≡ litFam c {K = K}
litFam-app c K = refl

-- `lits` is a fold of `_⊗ᶜ_` over `litCPS`: the empty word is `idCPS`...
litsCPS : (w : List Alphabet) → Dᶜ.CPS (lits w)
litsCPS [] = Dᶜ.idCPS
litsCPS (c ∷ w) = Dᶜ._⊗ᶜ_ (litCPS c) (litsCPS w)

-- ...so deciding a fixed word costs no new decision procedure, only `dec-ε`.
dec-lits : (w : List Alphabet) → Decidable (lits w)
dec-lits w = Dᶜ.atI (litsCPS w) dec-ε

------------------------------------------------------------------------
