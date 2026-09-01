{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The ascent motive is a quotient of the descent motive: at `K := Owes B`,
     Parser:  Ans (B ⊸ G)  ⇒  Ans (A ⊗ (B ⊸ G))
     Asc:     Ans (B ⊸ G)  ⇒  Ans ((B ⟜ A) ⊸ G)
   so a map of motives is a grammar map `A ⊗ (B ⊸ G) ⊢ (B ⟜ A) ⊸ G`, i.e.
   `Residual.⊸⟜-swap`: hence `descent→ascent`.  The converse map is refuted
   by `Ascent/Decidability.noShiftConverse`. -}
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

-- What `ascent→descent` would need: `⊸⟜-swap` with the turnstile reversed.
SwapConverse : Typeω
SwapConverse =
  {ℓ ℓ' ℓ'' : Level}
  {A : TheoryTy ℓ tt} {B : TheoryTy ℓ' tt} {C : TheoryTy ℓ'' tt}
  → (B ⟜ A) ⊸ C ⊢ A ⊗ (B ⊸ C)

-- `Decidability.noShiftConverse` is literally this schema at
-- `A := literal c`, `B := ⊥Ty`, `C := ⊥Ty`.
noSwapConverse : (c : Alphabet) → SwapConverse → εTy ⊢ ⊥Ty
noSwapConverse c sw = Dec.noShiftConverse c sw

module _ (𝒯 : AnswerFunctor) (cov : CovariantAnswer 𝒯)
  {ℓG : Level} (Goal : TheorySet ℓG tt) where

  open CovAscent 𝒯 cov Goal
  open Combinators 𝒯 using (Parser ; mkP ; pAt)

  -- the level `Owes B` lands in; `Parser`'s quantified `K` must reach it
  ℓOwes : Level → Level
  ℓOwes ℓB = ℓ-max ℓM (ℓ-max ℓB ℓG)

  -- sanity: `Owes` really does land there
  _ : {ℓB : Level} (B : TheorySet ℓB tt) → TheorySet (ℓOwes ℓB) tt
  _ = λ B → Owes B

  descent→ascent : {ℓB : Level} {a c : ParserTag} {A : TheorySet ℓA tt}
    → Parser (ℓOwes ℓB) a c A ⊢ Asc ℓB a c A
  descent→ascent {c = c} {A = A} =
    mkA λ B →
      ▷map {t = c}
        (Ans-map (⊸⟜-swap {A = ty A} {B = ty B} {C = ty Goal}))
      ∘⊢ pAt id⊢ (Owes B)

  -- Stated at `K := Owes B`, the only continuation where it typechecks; it
  -- is exactly `SwapConverse` away, and `noSwapConverse` refutes that.
  ascent→descentAt : SwapConverse
    → {ℓB : Level} {a c : ParserTag} {A : TheorySet ℓA tt}
      (B : TheorySet ℓB tt)
    → Asc ℓB a c A
    ⊢ (ty (▷? a (Ans (Owes B))) ⇒ ty (▷? c (Ans (A ⊗Set Owes B))))
  ascent→descentAt sw {c = c} {A = A} B =
    ⇒-intro
      (▷map {t = c} (Ans-map (sw {A = ty A} {B = ty B} {C = ty Goal}))
       ∘⊢ aAt id⊢ B)
