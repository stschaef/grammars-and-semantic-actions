{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Scratch: the ascent motive is a *quotient* of the descent motive.

   Instantiate `Core.Parser`'s quantified continuation `K` at `Owes B =
   B ⊸ Goal`.  Then the two bodies read

     Parser:  Ans (B ⊸ G)  ⇒  Ans (A ⊗ (B ⊸ G))
     Asc:     Ans (B ⊸ G)  ⇒  Ans ((B ⟜ A) ⊸ G)

   The *domains are identical*, so a map of motives is exactly a grammar map
     A ⊗ (B ⊸ G) ⊢ (B ⟜ A) ⊸ G
   and that is `Residual.⊸⟜-swap`, which is what `shift` is built from.

   Consequently a descent parser, taken at the continuations of residual
   shape, *is* an ascent parser: `descent→ascent` below.  The converse needs
   the converse grammar map, and that is precisely the one refuted by
   `Ascent/Decidability.noShiftConverse`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Ascent.Subsume
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  where

open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Combinator.Ascent.Base Alphabet _≟_
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using ( _⟜_ ; _⊸_ ; ⊸⟜-swap )
import Theory.Instances.Monoid.Combinator.Ascent.Decidability Alphabet _≟_
  as Dec

private variable ℓA ℓB ℓD : Level

-- The grammar map `ascent→descent` would need, as a schema.  `⊸⟜-swap` is
-- this with the turnstile the other way round.
SwapConverse : Typeω
SwapConverse =
  {ℓ ℓ' ℓ'' : Level}
  {A : TheoryTy ℓ tt} {B : TheoryTy ℓ' tt} {C : TheoryTy ℓ'' tt}
  → (B ⟜ A) ⊸ C ⊢ A ⊗ (B ⊸ C)

-- ...and it does not exist: `Decidability.noShiftConverse` is *literally*
-- this schema at `A := literal c`, `B := ⊥Ty`, `C := ⊥Ty`.
noSwapConverse : (c : Alphabet) → SwapConverse → εTy ⊢ ⊥Ty
noSwapConverse c sw = Dec.noShiftConverse c sw

module _ (𝒯 : AnswerFunctor) (cov : CovariantAnswer 𝒯)
  {ℓG : Level} (Goal : TheorySet ℓG tt) where

  open CovAscent 𝒯 cov Goal
  open Combinators 𝒯 using (Parser ; mkP ; pAt)

  -- the level `Owes B` lands in: `(ty B ⊸ ty Goal) m = (l : ↓M tt) → ...`,
  -- so the quantified `K` of `Parser` must be at least this big.
  ℓOwes : Level → Level
  ℓOwes ℓB = ℓ-max ℓM (ℓ-max ℓB ℓG)

  -- sanity: `Owes` really does land there
  _ : {ℓB : Level} (B : TheorySet ℓB tt) → TheorySet (ℓOwes ℓB) tt
  _ = λ B → Owes B

  -- THE POINT.  A descent parser, whose continuation ranges over *all* sets
  -- at `ℓOwes ℓB`, restricts to the residual ones and is then an ascent
  -- parser.  The only content is `⊸⟜-swap`.
  descent→ascent : {ℓB : Level} {a c : ParserTag} {A : TheorySet ℓA tt}
    → Parser (ℓOwes ℓB) a c A ⊢ Asc ℓB a c A
  descent→ascent {c = c} {A = A} =
    mkA λ B →
      ▷map {t = c}
        (Ans-map (⊸⟜-swap {A = ty A} {B = ty B} {C = ty Goal}))
      ∘⊢ pAt id⊢ (Owes B)

  -- THE CONVERSE, stated at the one continuation where it even typechecks
  -- (`K := Owes B`; there is no way to hit an arbitrary `K` at all, since
  -- `Asc` only ever produces answers of residual shape).  It is exactly
  -- `SwapConverse` away, and `noSwapConverse` says that is unavailable.
  ascent→descentAt : SwapConverse
    → {ℓB : Level} {a c : ParserTag} {A : TheorySet ℓA tt}
      (B : TheorySet ℓB tt)
    → Asc ℓB a c A
    ⊢ (ty (▷? a (Ans (Owes B))) ⇒ ty (▷? c (Ans (A ⊗Set Owes B))))
  ascent→descentAt sw {c = c} {A = A} B =
    ⇒-intro
      (▷map {t = c} (Ans-map (sw {A = ty A} {B = ty B} {C = ty Goal}))
       ∘⊢ aAt id⊢ B)
