{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Lookahead of arbitrary width for the ascent combinators.

   `Ascent/Base`'s `Predict` is hard-wired to `Λ₁`, the one-token cover, and so
   commits on one letter.  `Decidable/Lookahead`'s `Predictive` was never
   hard-wired -- it takes *any* `Cover Y Λ` -- and `Lookahead/Window` supplies
   the width-indexed family:

     Window n           the words of length at most `n`
     Λw : Window n → Grammar
     windowCover n : Cover (Window n) (Λw {n})

   So the generalisation is to take the same parameters on the ascent side.
   `WidePredict` is `Predict` with `M₁`, `Λ₁`, `Λ-total`, `Λ-disjoint` and
   `_≟M_` replaced by arguments; instantiating at `windowCover n` gives
   commitment on `n` tokens, and `n = w1` is the old behaviour.

   What this does and does not buy.  It moves the parser from LC(1) to LC(k)
   for whatever `k` a grammar needs -- `S → a A c | a B d`, `A → b`, `B → b`
   is out of reach at width 1 (both branches lead with `a`, so `altDisjoint`
   cannot be discharged) and in reach at width 3.  It does *not* reach LR:
   the commitment is still made at the start of a branch, and a grammar whose
   decision needs unboundedly much input -- `S → A b | B c`, `A → a A | a`,
   `B → a B | a`, which `LeftCorner/Defer` handles only by an ad-hoc trick --
   is outside LC(k) for every `k` while being SLR(1).  Widening the window
   does not defer the decision; only item sets do that. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Ascent.Lookahead
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  where

open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Combinator.Ascent.Base Alphabet _≟_ public
  hiding (_◂_)   -- `Suffix`s proper-suffix vs `Window`s cons
open import Theory.Instances.Monoid.Lookahead.Window Alphabet isSetAlphabet
  public
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (_⟜_ ; ⟜-precomp ; _⊸_ ; ⊸-precomp ; &⊕ᴰ-distR)
import Theory.Instances.Monoid.Combinator.Decidable.Window Alphabet _≟_ ℓ-zero
  as DW   -- only for `decWindow`: windows are discrete, and `◂` needs
          -- projection rather than matching, since `K` is off

private variable ℓB ℓC ℓD ℓY ℓΛ : Level

-- The cover-generic predictive choice.  Same shape as `Predictive`, with the
-- answer taken at `- ⊸ Goal` rather than at `- ⊗ K`.
module WidePredict (𝒯 : AnswerFunctor) (cov : CovariantAnswer 𝒯)
  {ℓG : Level} (Goal : TheorySet ℓG tt)
  {Y : Type ℓY}
  (_≟Y_ : (y y' : Y) → (y Eq.≡ y') Sum.⊎ ((y Eq.≡ y') → Empty.⊥))
  (Λ : Y → TheoryTy ℓΛ tt) (covr : Cover Y Λ)
  (C : Y → TheorySet ℓC tt)
  (lead : (y : Y) → ty (C y) ⊗ ⊤Ty ⊢ Λ y)
  where

  open Goto 𝒯 cov Goal public

  isSetY : isSet Y
  isSetY = DiscreteEq→isSet _≟Y_

  Alt : TheorySet _ tt
  Alt = ⊕ᴰSet isSetY C

  -- the condition, at whatever width the cover has
  altDisjoint : (y y' : Y) → (y Eq.≡ y' → Empty.⊥)
    → ty (C y) & ty (C y') ⊢ ⊥Ty
  altDisjoint y y' ne =
    covr .disjoint y y' ne
    ∘⊢ ((lead y ∘⊢ ⊗-unit-r⁻) ,&p (lead y' ∘⊢ ⊗-unit-r⁻))

  private
    commitW : (B : TheorySet ℓB tt)
      → ty (&ᴰSet (λ y → Ans (Owes (B ⟜Set C y))))
      ⊢ ty (Ans (Owes (B ⟜Set Alt)))
    commitW B =
      ⊕ᴰ-elim atCell ∘⊢ &⊕ᴰ-distR ∘⊢ (id⊢ ,& (covr .total ∘⊢ ⊤Ty-intro))
      where
      atCell : (y : Y)
        → ty (&ᴰSet (λ y' → Ans (Owes (B ⟜Set C y')))) & Λ y
        ⊢ ty (Ans (Owes (B ⟜Set Alt)))
      atCell y =
        Ans-map (⊸-precomp {A = ty B ⟜ ty (C y)} {A' = ty B ⟜ ty Alt}
                           {C = ty Goal}
                  (⟜-precomp {B = ty Alt} {B' = ty (C y)} {C = ty B} (σ⊕ y)))
        ∘⊢ π y ∘⊢ π₁

  chooseW : {a c : ParserTag} {D : TheoryTy ℓD tt}
    → ((y : Y) → D ⊢ Asc ℓB a c (C y)) → D ⊢ Asc ℓB a c Alt
  chooseW {c = c} p = mkA λ B →
    ▷map {t = c} (commitW B)
    ∘⊢ ▷laxᴰ (λ y → Ans (Owes (B ⟜Set C y)))
    ∘⊢ (&ᴰ-intro λ y → aAt (p y) B)

-- ...and LR(k): the same parser, committing on `n` tokens.
module WidthPredict (𝒯 : AnswerFunctor) (cov : CovariantAnswer 𝒯)
  {ℓC : Level}
  {ℓG : Level} (Goal : TheorySet ℓG tt) (n : Width)
  (C : Window n → TheorySet ℓC tt)
  (lead : (w : Window n) → ty (C w) ⊗ ⊤Ty ⊢ Λw w)
  = WidePredict 𝒯 cov Goal DW.decWindow (Λw {n}) (windowCover n) C lead
