{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
-- Leftmost-longest match, with no automaton: `Grammar/Greedy/Base.agda`
-- states this over a `Trace`.
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Greedy.Base
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Unit using (tt ; tt*)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.List using ([] ; _∷_ ; _++_)
import Cubical.Data.List.Properties as L
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Precise Alphabet isSetAlphabet using (flat ; flatEq)
open import Theory.Type.Decidable.Base MonEqns Alphabet (λ _ → tt)
  listPresentation

private variable ℓA ℓB : Level

char⁺ : TheoryTy _ tt
char⁺ = char ⊗ String*

module _ (A : TheoryTy ℓA tt) where
  -- A parse of `A` over some `w`, plus a refutation of every nonempty
  -- extension of `w`.  The extension is `⌈ w ⌉ ⊸ A`, not `A ⟜ ⌈ w ⌉`.
  Greedy : TheoryTy _ tt
  Greedy =
    ⊕[ w ∈ String ]
      ((⌈ w ⌉ & A) ⊗ ¬Ty (((⌈ w ⌉ ⊸ A) & char⁺) ⊗ ⊤Ty))

  Greedy→leftmost : Greedy ⊢ A ⊗ ⊤Ty
  Greedy→leftmost = ⊕ᴰ-elim λ w → π₂ ,⊗ ⊤Ty-intro

  GreedyCompl : TheoryTy _ tt
  GreedyCompl = ¬Ty (A ⊗ ⊤Ty)

  disjointGreedy-GreedyCompl : Greedy & GreedyCompl ⊢ ⊥Ty
  disjointGreedy-GreedyCompl =
    ⇒-app ∘⊢ &-swap ∘⊢ (Greedy→leftmost ,&p id⊢)

-- `Grammar/Greedy/Regex.agda`'s `no-nonempty-extension-step` (a hole there)
-- with the automaton removed; the precision of `literal c` replaces
-- step-inversion.
noExt-step : (c : Alphabet) {A : TheoryTy ℓA tt}
  → literal c ⊗ ¬Ty ((literal c ⊸ A) ⊗ ⊤Ty)
  ⊢ ¬Ty ((A & char⁺) ⊗ ⊤Ty)
noExt-step c {A = A} m (ms , e , (lc , (nk , _))) t =
  nk (two ks1 ns1 , Eq.pathToEq tail≡ , (resid , (tt , tt*)))
  where
  ns = t .fst
  a : A (ns zero)
  a = t .snd .snd .fst .fst

  pl = t .snd .snd .fst .snd
  ks = pl .fst
  d  = pl .snd .snd .fst .fst
  ks1 = ks (suc zero)
  ns1 = ns (suc zero)

  headed : d ∷ ks1 ≡ ns zero
  headed = flat d (ks zero) ks1 (ns zero) (pl .snd .snd .fst .snd) (pl .snd .fst)

  whole : c ∷ ms (suc zero) ≡ d ∷ (ks1 ++ ns1)
  whole = flat c (ms zero) (ms (suc zero)) m lc e
        ∙ sym (cong (_++ ns1) headed ∙ Eq.eqToPath (t .snd .fst))

  c≡d : c ≡ d
  c≡d = L.cons-inj₁ whole

  tail≡ : ks1 ++ ns1 ≡ ms (suc zero)
  tail≡ = sym (L.cons-inj₂ whole)

  resid : (literal c ⊸ A) ks1
  resid l ll = subst A shape a
    where
    shape : ns zero ≡ l ++ ks1
    shape = sym headed
          ∙ cong (_∷ ks1) (sym c≡d)
          ∙ sym (cong (_++ ks1) (Eq.eqToPath ll))

-- `Greedy` indexed by the residual, so `extendAt` is O(1) instead of
-- rebuilding at `c ∷ w`.  `R` is a parameter: this is only ABOUT greediness
-- when `R` is A's residual after the match (`δ-sound`/`δ-complete`).

open import Theory.Instances.Monoid.Derivative Alphabet isSetAlphabet
  using (Dl)

module _ (c : Alphabet) where
  -- `flatEq`, not `flat`: a cubical `subst` leaves a `transp` over the
  -- splitting that never reduces, so the match could not be read back out.
  lit⊗Dl : {A : TheoryTy ℓA tt} → literal c ⊗ Dl c A ⊢ A
  lit⊗Dl {A = A} m (ms , e , (lc , (a , _))) =
    Eq.transport A (flatEq c (ms zero) (ms (suc zero)) m lc e) a

GreedyAt : (A : TheoryTy ℓA tt) (R : TheoryTy ℓB tt) → TheoryTy _ tt
GreedyAt A R = A ⊗ ¬Ty ((R & char⁺) ⊗ ⊤Ty)

module _ {A : TheoryTy ℓA tt} {R : TheoryTy ℓB tt} where
  extendAt : (c : Alphabet)
    → literal c ⊗ GreedyAt (Dl c A) R ⊢ GreedyAt A R
  extendAt c = (lit⊗Dl c ,⊗ id⊢) ∘⊢ ⊗-assoc⁻

  GreedyAt→prefix : GreedyAt A R ⊢ A ⊗ ⊤Ty
  GreedyAt→prefix = id⊢ ,⊗ ⊤Ty-intro
