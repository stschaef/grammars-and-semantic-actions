{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A deterministic automaton is a grammar family whose transition is the
   derivative.

   That is the whole content of the interface below: `L q` is the language
   read from state `q`, and `δ q c` is required to *be* the derivative of
   `L q` by `c` -- stated with `∂[ literal c ]`, the general derivative,
   rather than with `Dl` directly.  Brzozowski's construction is then one
   instance among others, and `Derivative/General`'s coincidence theorem
   is what lets the proofs below still compute with `Dl`.

   The point of naming the state set is sharing.  A run over `n`
   characters visits `n` states, not `n` prefixes, so a table indexed by
   `Q` carries every state at once -- which is what makes a scan one pass
   rather than one pass per candidate match. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Automaton.Base
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using ([] ; _∷_ ; _++_)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Derivative Alphabet isSetAlphabet
  using (Dl ; Dl-string)
open import Theory.Instances.Monoid.Derivative.General Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet using (_⊸_)
open import Theory.Type.Decidable.Base MonEqns Alphabet (λ _ → tt)
  listPresentation
open import Theory.Type.HLevels MonEqns Alphabet (λ _ → tt) listPresentation
  using (isSetTheoryTy)

private variable ℓQ ℓL : Level

------------------------------------------------------------------------
-- The interface.

record DerivAutomaton (ℓQ ℓL : Level) : Type (ℓ-suc (ℓ-max ℓAlph (ℓ-max ℓQ ℓL))) where
  field
    Q : Type ℓQ
    δ : Q → Alphabet → Q

    -- the language read from a state
    L : Q → TheoryTy ℓL tt

    -- ...whose transition is the derivative, in both directions.  Stated
    -- through `∂`; `literal c` is representable, so this is `Dl` by
    -- `∂⌈⌉→Dl`/`Dl→∂⌈⌉` and nothing else needs to know.
    δ-∂  : (q : Q) (c : Alphabet) → ∂[ literal c ] (L q) ⊢ L (δ q c)
    δ-∂⁻ : (q : Q) (c : Alphabet) → L (δ q c) ⊢ ∂[ literal c ] (L q)

    -- acceptance, as data plus its two internal readings
    -- enough to fix the fold's carrier
    isSetQ : isSet Q
    isSetL : (q : Q) → isSetTheoryTy (L q)

    acc  : Q → Bool
    accY : (q : Q) → acc q Eq.≡ true  → εTy ⊢ L q
    accN : (q : Q) → acc q Eq.≡ false → L q & εTy ⊢ ⊥Ty

  -- The square in Brzozowski form.  `literal c` is `⌈ ⌈gen c ⌉ ⌉`, so
  -- this is the coincidence theorem of `Derivative/General` and not a
  -- second definition of anything.
  δ-Dl : (q : Q) (c : Alphabet) → Dl c (L q) ⊢ L (δ q c)
  δ-Dl q c = δ-∂ q c ∘⊢ Dl→∂⌈⌉ (⌈gen c ⌉)

  δ-Dl⁻ : (q : Q) (c : Alphabet) → L (δ q c) ⊢ Dl c (L q)
  δ-Dl⁻ q c = ∂⌈⌉→Dl (⌈gen c ⌉) ∘⊢ δ-∂⁻ q c

  -- ...and the residual form, which is what a refutation of "nothing
  -- longer matches" consumes.  Also the coincidence theorem, at `⊸`.
  δ-⊸ : (q : Q) (c : Alphabet) → L (δ q c) ⊢ literal c ⊸ L q
  δ-⊸ q c = ∂⌈⌉→⊸ (⌈gen c ⌉) ∘⊢ δ-∂⁻ q c

  δ-⊸⁻ : (q : Q) (c : Alphabet) → literal c ⊸ L q ⊢ L (δ q c)
  δ-⊸⁻ q c = δ-∂ q c ∘⊢ ⊸→∂⌈⌉ (⌈gen c ⌉)

  -- the state after a whole word
  δ* : Q → String → Q
  δ* q [] = q
  δ* q (c ∷ w) = δ* (δ q c) w
