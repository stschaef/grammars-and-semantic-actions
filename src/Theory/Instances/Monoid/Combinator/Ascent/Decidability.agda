{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- What has to be generalised before the ascent combinators can decide.

   Every use of covariance in `Ascent/Base` is a map along some term.  Seven of
   the nine have a converse, so they only want `DivariantAnswer` -- which
   `Dec` has -- or the answer's own primitive:

     `reduce`   `⊸-precomp (⟜-precomp p)`  -- invertible iff `p` is, so take
                                              both directions, as `mapP` does
     `goto`     `⊸-precomp ⟜-curry`        -- associativity; converse exists
     `nil`      `⊸-precomp ⟜-unitr`        -- unit; converse is `⟜-unitr⁻`
     `pick`     `⊕-elim id id`             -- `inl` backwards; `dec-map`
                                              takes it
     `runA`     `start`                    -- converse exists
     `failA`    `Ans-empty`                -- `Dec` refutes `⊥` outright
     `chooseA`  `⊸-precomp (⟜-precomp (σ⊕ o))`
                                           -- should go through `Ans-route`,
                                              which `Dec` has, not a map

   Two do not, and they fail for one reason.  `Owes B = B ⊸ Goal` puts a
   *universal quantifier inside the grammar* -- over every stack, at every
   string -- and a universal over an unbounded domain can be vacuously true,
   so there is nothing to refute:

     `shift`  needs `(B ⟜ literal c) ⊸ Goal ⊢ literal c ⊗ (B ⊸ Goal)`.
              False: when no stack absorbs a `c`, the left side holds
              vacuously at a word that does not begin with `c`.
     `runA`   needs `(Goal ⊸ Goal) ⊢ εTy`.  False for the same reason: at a
              non-empty word `Goal ⊸ Goal` holds vacuously when `Goal` is
              empty, so "the input is not finished" cannot be refuted.

   Note what is *not* the problem.  `Core.Parser`'s `&[K]` is also a
   quantification, but it is at the metalanguage level over a grammar
   parameter, and the grammar it decides -- `A ⊗ K` -- is positive.  `Dec`
   lives with that happily.  It is `⊸` putting the quantifier *inside* the
   grammar that it cannot survive.

   So the generalisation is not in the answer functor.  It is in what the
   parser's state is.  Replacing the residual by the *derivative* fixes it:
   `Dl-string w A m = A (w ++ m)` is the goal left-quotiented by what has
   been read, and it is positive -- no quantifier inside.  The two terms
   below are the evidence: at the derivative, shift has a converse, which is
   exactly what `⊸⟜-swap` lacks. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Ascent.Decidability
  {ℓAlph} (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)) where

open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Combinator.Core Alphabet _≟_
open import Theory.Instances.Monoid.SequentialUnambiguity.Nullable Alphabet isSetAlphabet
  using (¬Nullable ; ¬Nullable-map)
open import Theory.Instances.Monoid.SequentialUnambiguity.First Alphabet isSetAlphabet
  using (¬Nullable-startsWith)
import Theory.Instances.Monoid.Combinator.Ascent.Base Alphabet _≟_ as A
import Theory.Instances.Monoid.Combinator.Decidable.Base Alphabet _≟_ ℓ-zero as D
open import Theory.Instances.Monoid.Derivative Alphabet isSetAlphabet
  using (Dl-string)
open import Theory.Instances.Monoid.Precise Alphabet isSetAlphabet
  using (Dl-absorb ; Dl-absorb⁻)
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using ( _⟜_ ; _⊸_ ; ⟜-precomp ; ⊸-lam ; ⊸-precomp ; ⊗ε-unit-r )

private variable ℓ : Level

-- SHIFT at the derivative, in both directions.  Both terms match on a
-- splitting, so they live in `Precise` beside `Dl-lit⊗`; here they are only
-- named, so the point they make -- that shift *has* a converse once the
-- state is a derivative, which `⊸⟜-swap` lacks -- can be read off.
shiftD : {A : TheoryTy ℓ tt} (c : Alphabet) (w : String)
  → literal c ⊗ Dl-string (w ++ (c ∷ [])) A ⊢ Dl-string w A
shiftD {A = A} = Dl-absorb {A = A}

shiftD⁻ : {A : TheoryTy ℓ tt} (c : Alphabet) (w : String)
  → Λ₁ (tk c) & Dl-string w A ⊢ literal c ⊗ Dl-string (w ++ (c ∷ [])) A
shiftD⁻ {A = A} = Dl-absorb⁻ {A = A}

-- ---------------------------------------------------------------------------
-- The obstruction, machine-checked rather than argued.
--
-- `shift` maps along `⊸⟜-swap : A ⊗ (B ⊸ C) ⊢ (B ⟜ A) ⊸ C`.  `Dec` needs the
-- converse to move a refutation backwards.  There is none, and here is why:
-- take the stack `⊥Ty`, which no word inhabits.  Then `⊥Ty ⟜ literal c` is
-- empty -- it would have to turn a `c` into a `⊥Ty` -- so
-- `(⊥Ty ⟜ literal c) ⊸ ⊥Ty` is inhabited *vacuously*, at every word,
-- including the empty one.  But `literal c ⊗ (⊥Ty ⊸ ⊥Ty)` is not inhabited
-- at the empty word: it demands a `c` be there.
--
-- So the left side holds where the right side does not, and no `⊢`-term can
-- go that way.  The vacuity is the whole point: `B ⊸ Goal` is a universal
-- over stacks, and a universal over an unbounded domain cannot be refuted.

module _ (c : Alphabet) where

  -- `⊥Ty ⟜ literal c` is empty: absorbing a `c` would produce a `⊥Ty`.  The
  -- only step outside the combinators is applying the stack at `⌈gen c ⌉`,
  -- which *constructs* a word from a letter rather than taking one apart.
  noStack : ⊥Ty ⟜ literal c ⊢ ⊥Ty
  noStack l s = s (⌈gen c ⌉) Eq.refl

  -- ...so the left-hand side is inhabited at the empty word, vacuously.
  vacuous : εTy ⊢ (⊥Ty ⟜ literal c) ⊸ ⊥Ty
  vacuous =
    ⊸-lam {A = ⊥Ty ⟜ literal c} {B = εTy} {C = ⊥Ty} (noStack ∘⊢ ⊗ε-unit-r)

  -- ...and the right-hand side is not, because it is headed by a letter.
  -- That is `¬Nullable`, which the repo already states as a `⊢`-term and
  -- already proves for `startsWith`.
  notThere : ¬Nullable (literal c ⊗ (⊥Ty ⊸ ⊥Ty))
  notThere = ¬Nullable-map (⊗-map id⊢ ⊤Ty-intro) (¬Nullable-startsWith {c})

  -- THEREFORE: `⊸⟜-swap` has no converse, so `Ans-dimap` cannot be used for
  -- `shift`, so `Dec` cannot instantiate the ascent combinators as they
  -- stand.  This is not a missing lemma; it is a counterexample -- and the
  -- absurdity it lands in is itself a `⊢`-term: the empty word would be
  -- empty.
  noShiftConverse :
    ((⊥Ty ⟜ literal c) ⊸ ⊥Ty ⊢ literal c ⊗ (⊥Ty ⊸ ⊥Ty)) → εTy ⊢ ⊥Ty
  noShiftConverse f = notThere ∘⊢ ((f ∘⊢ vacuous) ,& id⊢)

-- ---------------------------------------------------------------------------
-- The other half: the sites that are *not* blocked.  The converses `Dec` needs
-- are all internal and none of them is about parsing, so they live in
-- `Residual` with the terms they invert -- `⟜-curry⁻`, `⟜-unitr⁻`.  What is
-- left here is the one that *is* about parsing: the reduction, the heart of
-- the thing, at `DivariantAnswer` instead of `CovariantAnswer`.

private variable ℓA ℓB ℓC ℓD : Level

-- The reduction -- the heart of the thing -- at `DivariantAnswer` instead of
-- `CovariantAnswer`.  Two maps instead of one, exactly as `mapP` takes for
-- the descent side.
module DivReduce (𝒯 : AnswerFunctor) (div : DivariantAnswer 𝒯)
  {ℓG : Level} (Goal : TheorySet ℓG tt) where
  open A.Ascent 𝒯 Goal
  open DivariantAnswer div

  reduce± : {ℓB ℓβ ℓA' : Level} {a c : ParserTag}
    {β : TheorySet ℓβ tt} {A : TheorySet ℓA' tt}
    → ty β ⊢ ty A → ty A ⊢ ty β
    → Asc ℓB a c β ⊢ Asc ℓB a c A
  reduce± {c = c} {β = β} {A = A} p q = mkA λ B →
    ▷map {t = c}
      (Ans-dimap {A = Owes (B A.⟜Set β)} {B = Owes (B A.⟜Set A)}
        (⊸-precomp {A = ty B ⟜ ty β} {A' = ty B ⟜ ty A} {C = ty Goal}
          (⟜-precomp {B = ty A} {B' = ty β} {C = ty B} p))
        (⊸-precomp {A = ty B ⟜ ty A} {A' = ty B ⟜ ty β} {C = ty Goal}
          (⟜-precomp {B = ty β} {B' = ty A} {C = ty B} q)))
    ∘⊢ aAt id⊢ B

-- ...and it instantiates at `Dec`.  Nothing about the answer functor was in
-- the way; only `shift` and `runA` were, for the reason refuted above.
module DecReduce = DivReduce D.DecAnswer D.DecDiv εSet
