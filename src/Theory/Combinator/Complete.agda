{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Completeness, as a cover.

   The framework has been proving completeness by hand, one client at a
   time, next to a mechanism that hands it over.  `Theory/Type/Decidable/
   Base` already has

     DecCover A true = A ;  DecCover A false = ¬Ty A
     decisionCover  : Decidable A → Cover Bool (DecCover A)
     coverDecidable : Cover Bool (DecCover A) → Decidable A

   so a DECISION and a COVER OF `Bool` are the same thing, and under that
   identification the cover's two laws are the two halves of what a checker
   owes:

     `total`     every element is an `A` or a refutation of `A`
                 -- soundness and COMPLETENESS together
     `disjoint`  never both -- consistency

   That is the whole content of "prove completeness by mapping into a
   total, disjoint disjunction".  Neither name occurred anywhere in
   `Theory/Combinator/` or in any client before this module.

   `decideCell` below is the direction that does work rather than merely
   restating.  A cover over ANY discrete index makes EVERY cell decidable:
   `total` names the cell the element is in, and for any other cell
   `disjoint` refutes it.  So the discipline for a new judgment is

     exhibit the judgment as a CELL of a cover of the model,

   and the checker, its soundness and its completeness all come out of the
   cover's two fields.  Where the framework already uses a cover for case
   analysis (`look`, which consumes `total` alone), this consumes both --
   the same object, read twice.

   What this does NOT do is make completeness free.  Building the cover is
   the work; `total` is exactly as hard to prove as completeness was,
   because it IS completeness.  The gain is that it is now one obligation
   with a name and a shape, discharged by the same construction that gives
   the decision, rather than a bespoke induction written afterwards and
   related to the checker only by hand. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Combinator.Complete
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Bool using (Bool ; true ; false)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Cover.Base σeq V vs 𝒫 public
  using (Cover ; total ; disjoint ; cover-elim)
open import Theory.Type.Decidable.Base σeq V vs 𝒫 public
  using (Decidable ; DecTy ; ¬Ty ; dec-yes ; dec-no
        ; DecCover ; decisionCover ; coverDecidable ; dec-cover)
-- `DiscreteEq` is stated inline in `Route`; restate it rather than
-- reach into that module, since nothing else here needs routing.
DiscreteEq : {ℓY : Level} → Type ℓY → Type ℓY
DiscreteEq Y = (y y' : Y) → (y Eq.≡ y') Sum.⊎ ((y Eq.≡ y') → Empty.⊥)

private variable ℓA ℓY : Level

-- A decision IS a cover of `Bool`, both ways.  `asCover` reads a checker as
-- the disjunction it decides; `fromCover` reads a disjunction as a checker.
module _ {s : S} {A : TheoryTy ℓA s} where

  asCover : Decidable A → Cover Bool (DecCover A)
  asCover = decisionCover

  fromCover : Cover Bool (DecCover A) → Decidable A
  fromCover = coverDecidable

-- ...and the direction that does work.  Exhibit your judgment as a cell of
-- a cover and the checker falls out, completeness included -- `total` is
-- where it lives, `disjoint` is what refutes the cells not taken.
decideCell : {s : S} {Y : Type ℓY} {Λ : Y → TheoryTy ℓA s}
  → DiscreteEq Y → Cover Y Λ → (y : Y) → Decidable (Λ y)
decideCell decY cov = dec-cover decY cov
