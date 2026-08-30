{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Decidable.Window
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Combinator.Decidable.Routed Alphabet _≟_ ℓ public
  hiding (_◂_)
open import Theory.Instances.Monoid.Lookahead.Window Alphabet isSetAlphabet
  public

-- windows are discrete whenever the alphabet is, at every width.  `◂` is
-- inverted by projection rather than by matching: `K` is off, so an
-- equation between constructor applications does not split.
private
  hdOr : Alphabet → {n : Width} → Window (more n) → Alphabet
  hdOr a ⟨⟩ = a
  hdOr a (c ◂ _) = c

  tlOr : {n : Width} → Window n → Window (more n) → Window n
  tlOr v ⟨⟩ = v
  tlOr v (_ ◂ w) = w

decWindow : {n : Width} → DiscreteEq (Window n)
decWindow ⟨⟩ ⟨⟩ = Sum.inl Eq.refl
decWindow ⟨⟩ (c ◂ w') = Sum.inr λ ()
decWindow (c ◂ w) ⟨⟩ = Sum.inr λ ()
decWindow (c ◂ w) (d ◂ w') = onHeadAndTail (c ≟ d) (decWindow w w')
  where
  onHeadAndTail : (c Eq.≡ d) Sum.⊎ ((c Eq.≡ d) → Empty.⊥)
     → (w Eq.≡ w') Sum.⊎ ((w Eq.≡ w') → Empty.⊥)
     → ((c ◂ w) Eq.≡ (d ◂ w')) Sum.⊎ (((c ◂ w) Eq.≡ (d ◂ w')) → Empty.⊥)
  onHeadAndTail (Sum.inl Eq.refl) (Sum.inl Eq.refl) = Sum.inl Eq.refl
  onHeadAndTail (Sum.inl Eq.refl) (Sum.inr nw) =
    Sum.inr λ e → nw (Eq.ap (tlOr w) e)
  onHeadAndTail (Sum.inr nc) _ = Sum.inr λ e → nc (Eq.ap (hdOr c) e)

-- Coarsening the width-`n` cover.  `PushOf` is where the width enters and
-- the only place it does: `Route`, `routeIn`, `choose` and the fixpoint are
-- unchanged, at every `n`.
module PushW (n : Width) {Y : Type ℓAlph} (r : Window n → Maybe Y) =
  PushOf ℓG (Λw {n}) (windowCover n) decWindow r
