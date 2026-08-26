{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Precision of the token grammars: a splitting whose left factor is a
   letter is determined by the whole word, so a refutation of the right
   factor refutes the tensor.  This is what turns a decision under a token
   into a decision of the tensor, and it is a fact about `literal`/`char`,
   not about any parser. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Precise
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.List using ([] ; _∷_ ; _++_)
import Cubical.Data.List.Properties as L
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Derivative Alphabet isSetAlphabet using (Dl)
open import Theory.Type.Decidable.Base MonEqns Alphabet (λ _ → tt)
  listPresentation

private variable ℓA ℓB : Level

-- The head letter cannot be matched away -- `(c ∷ []) ++ v ≟ c ∷ as` would
-- eliminate the reflexive equation `c = c`, which K forbids -- so the split
-- is flattened to a path and read off by cons-injectivity.
flat : (c : Alphabet) (u v w : ↓M tt)
  → u Eq.≡ (c ∷ []) → (u ++ v) Eq.≡ w → c ∷ v ≡ w
flat c u v w lc e = cong (_++ v) (sym (Eq.eqToPath lc)) ∙ Eq.eqToPath e

-- The same fact in the Eq world.  `flat` composes its two inputs with `∙`,
-- so a `subst` along it is a stuck `transp` even when both are `Eq.refl`;
-- `Eq.transport A Eq.refl a = a` holds on the nose, which is what lets a
-- witness transported through it be projected back out.
flatEq : (c : Alphabet) (u v w : ↓M tt)
  → u Eq.≡ (c ∷ []) → (u ++ v) Eq.≡ w → (c ∷ v) Eq.≡ w
flatEq c u v w Eq.refl Eq.refl = Eq.refl

-- Under a derivative, `ε` is refuted and a leading literal is pinned:
-- these are the two ways a one-step unrolling meets `Dl`, and both are
-- the precision of `literal` again.
Dl-ε : (c : Alphabet) → Dl c εTy ⊢ ⊥Ty
Dl-ε c m e = Empty.rec (L.¬nil≡cons (Eq.eqToPath (e .snd .fst)))

Dl-lit⊗ : (c d : Alphabet) {X : TheoryTy ℓA tt}
  → Dl c (literal d ⊗ X) ⊢ ⊕[ _ ∈ d ≡ c ] X
Dl-lit⊗ c d {X = X} m (ms , e , l , x , _) =
  L.cons-inj₁ headed , subst X (L.cons-inj₂ headed) x
  where
  headed : d ∷ ms (suc zero) ≡ c ∷ m
  headed = flat d (ms zero) (ms (suc zero)) (c ∷ m) l e

lit⊗-nil : {X : Type ℓA} (c : Alphabet) (u v : ↓M tt)
  → u Eq.≡ (c ∷ []) → (u ++ v) Eq.≡ [] → X
lit⊗-nil c u v lc e = Empty.rec (L.¬cons≡nil (flat c u v [] lc e))

lit⊗-head : {X : Type ℓA} (c a : Alphabet) (u v as : ↓M tt)
  → (a Eq.≡ c → Empty.⊥)
  → u Eq.≡ (c ∷ []) → (u ++ v) Eq.≡ (a ∷ as) → X
lit⊗-head c a u v as ne lc e =
  Empty.rec (ne (Eq.pathToEq (sym (L.cons-inj₁ (flat c u v (a ∷ as) lc e)))))

lit⊗-tail : {B : TheoryTy ℓA tt} (c : Alphabet) (u v as : ↓M tt)
  → u Eq.≡ (c ∷ []) → (u ++ v) Eq.≡ (c ∷ as) → B v → B as
lit⊗-tail {B = B} c u v as lc e =
  subst B (L.cons-inj₂ (flat c u v (c ∷ as) lc e))

-- `literal c` is precise: two splittings with the same one-letter prefix
-- agree on the suffix, so refuting the suffix refutes the whole tensor.
lit⊗-precise : {K : TheoryTy ℓA tt} (c : Alphabet)
  → literal c ⊗ ¬Ty K ⊢ ¬Ty (literal c ⊗ K)
lit⊗-precise {K = K} c m (ms , e , (lc , (nk , _))) t =
  nk (subst K (sym (L.cons-inj₂ tails)) (t .snd .snd .snd .fst))
  where
  ns = t .fst
  tails : c ∷ ms (suc zero) ≡ c ∷ ns (suc zero)
  tails = flat c (ms zero) (ms (suc zero)) m lc e
        ∙ sym (flat c (ns zero) (ns (suc zero)) m
                 (t .snd .snd .fst) (t .snd .fst))

-- ...and so is `char`, which fixes the splitting without fixing the letter
char⊗-precise : {K : TheoryTy ℓA tt} → char ⊗ ¬Ty K ⊢ ¬Ty (char ⊗ K)
char⊗-precise {K = K} m (ms , e , ((d , lc) , (nk , _))) t =
  nk (subst K (sym (L.cons-inj₂ tails)) (t .snd .snd .snd .fst))
  where
  ns = t .fst
  tails : d ∷ ms (suc zero) ≡ t .snd .snd .fst .fst ∷ ns (suc zero)
  tails = flat d (ms zero) (ms (suc zero)) m lc e
        ∙ sym (flat (t .snd .snd .fst .fst) (ns zero) (ns (suc zero)) m
                 (t .snd .snd .fst .snd) (t .snd .fst))

-- The one-token derivative as a term rather than a case split: a decision
-- under the letter is a decision of the tensor.
dec-lit⊗↑ : {K : TheoryTy ℓA tt} (c : Alphabet)
  → literal c ⊗ DecTy K ⊢ DecTy (literal c ⊗ K)
dec-lit⊗↑ c = ⊕-elim dec-yes (dec-no ∘⊢ lit⊗-precise c) ∘⊢ ⊗⊕-distR

dec-char⊗↑ : {K : TheoryTy ℓA tt} → char ⊗ DecTy K ⊢ DecTy (char ⊗ K)
dec-char⊗↑ = ⊕-elim dec-yes (dec-no ∘⊢ char⊗-precise) ∘⊢ ⊗⊕-distR
