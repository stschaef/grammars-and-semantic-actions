{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `WidePredict` is `Ascent/Base`'s `Predict` with the one-token cover an
   argument; `windowCover n` commits on n tokens: LC(1) → LC(k).
   `S → a A c | a B d`, `A → b`, `B → b` needs width 3.  Not LR: commitment
   stays at branch start -- `S → A b | B c`, `A → a A | a`, `B → a B | a`
   is outside LC(k) for every k yet SLR(1). -}
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
  using (_⟜_ ; ⟜-precomp ; _⊸_ ; ⊸-precomp)
import Theory.Instances.Monoid.Combinator.Decidable.Window Alphabet _≟_ ℓ-zero
  as DW   -- only for `decWindow`

private variable ℓB ℓC ℓD ℓY ℓΛ : Level

-- `Predictive`'s shape, with the answer at `- ⊸ Goal` rather than `- ⊗ K`.
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
