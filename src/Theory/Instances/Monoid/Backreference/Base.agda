{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The dependent tensor, and backreferences.

   `⊗ᴰ A B` is `A ⊗ B` where the right factor may mention the string `l` that
   the left factor consumed and the tree `a : A l` it built over it.  Taking
   `B l a = ⌈ l ⌉` -- the representable at `l` -- is a backreference: match
   `A`, then match its own yield again, literally.

   Like `Residual.agda`, this file introduces a connective by matching on its
   own elements; nothing downstream of it binds a model element. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Backreference.Base
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List as L using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Sigma using (_,_ ; _×_ ; Σ-syntax ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; Unit* ; tt ; tt*)
import Cubical.Data.Sum as Sum
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet

private variable ℓ ℓ' ℓ'' : Level

-- A right factor that may read the left factor's parse.
Dep : TheoryTy ℓ tt → (ℓ' : Level) → Type _
Dep A ℓ' = (l : String) → A l → TheoryTy ℓ' tt

-- The same shape as `_⊗_`: a splitting, an equation, and the two slots --
-- except the slots are a Σ rather than a ×, so the second may see the first.
⊗ᴰ : (A : TheoryTy ℓ tt) → Dep A ℓ' → TheoryTy (ℓ-max ℓM (sup 2 (two ℓ ℓ'))) tt
⊗ᴰ A B m =
  Σ[ ms ∈ interpIn _⊙_ ↓M ]
    (op _⊙_ ms Eq.≡ m)
    × (Σ[ a ∈ A (ms zero) ] (B (ms zero) a (ms (suc zero)) × Unit* {ℓ-zero}))

-- Conservativity: when the right factor ignores the tree, this *is* `_⊗_`.
-- A `Σ` over a constant family is a `×`, so the two are the same type.
⊗ᴰ-const : {A : TheoryTy ℓ tt} {B : TheoryTy ℓ' tt}
  → ⊗ᴰ A (λ _ _ → B) ≡ A ⊗ B
⊗ᴰ-const = refl
-- Associativity with a prefix-indexed right factor.

-- `seq` reassociates `A ⊗ (B ⊗ K)` with `⊗-assoc`/`⊗-assoc⁻`.  The same
-- shuffle with the continuation indexed by what was consumed: the index
-- splits into the two prefixes, `l₁` and `l₁ ++ l₂`.  These are `⊗-assoc`
-- of `Strings.agda` with the `C` slot re-indexed; the splits are identical.
module _ {A : TheoryTy ℓ tt} {B : String → TheoryTy ℓ' tt}
  {C : String → TheoryTy ℓ'' tt}
  where
  ⊗ᴰ-assoc :
    ⊗ᴰ (⊗ᴰ A (λ l _ → B l)) (λ l _ → C l)
    ⊢ ⊗ᴰ A (λ l₁ _ → ⊗ᴰ (B l₁) (λ l₂ _ → C (l₁ ++ l₂)))
  ⊗ᴰ-assoc m (ms , e , ((ns , f , (a , (b , _))) , (c , _))) =
    two (ns zero) (ns (suc zero) ++ ms (suc zero))
      , split
      , (a , ((two (ns (suc zero)) (ms (suc zero)) , Eq.refl
              , (b , (castEq {A = λ x → C x (ms (suc zero))} (Eq.sym f) c
                     , tt*))) , tt*))
    where
    split : (ns zero ++ (ns (suc zero) ++ ms (suc zero))) Eq.≡ m
    split = Eq.sym (++-assocEq (ns zero) (ns (suc zero)) (ms (suc zero)))
       Eq.∙ (Eq.ap (_++ ms (suc zero)) f Eq.∙ e)

  ⊗ᴰ-assoc⁻ :
    ⊗ᴰ A (λ l₁ _ → ⊗ᴰ (B l₁) (λ l₂ _ → C (l₁ ++ l₂)))
    ⊢ ⊗ᴰ (⊗ᴰ A (λ l _ → B l)) (λ l _ → C l)
  ⊗ᴰ-assoc⁻ m (ms , e , (a , ((ns , f , (b , (c , _))) , _))) =
    two (ms zero ++ ns zero) (ns (suc zero))
      , split
      , ((two (ms zero) (ns zero) , Eq.refl , (a , (b , tt*))) , (c , tt*))
    where
    split : ((ms zero ++ ns zero) ++ ns (suc zero)) Eq.≡ m
    split = ++-assocEq (ms zero) (ns zero) (ns (suc zero))
       Eq.∙ (Eq.ap (ms zero ++_) f Eq.∙ e)

-- `⊗ᴰ` is functorial in its left factor, at a fixed indexed continuation.
⊗ᴰ-mapL : {A : TheoryTy ℓ tt} {B : TheoryTy ℓ' tt}
  {C : String → TheoryTy ℓ'' tt}
  → A ⊢ B → ⊗ᴰ A (λ l _ → C l) ⊢ ⊗ᴰ B (λ l _ → C l)
⊗ᴰ-mapL f m (ms , e , (a , (cont , _))) = ms , e , (f (ms zero) a , (cont , tt*))

-- `<|>` needs distribution over the sum; the index sees only the string,
-- so the two summands' trees never have to be reconciled.
module _ {A : TheoryTy ℓ tt} {B : TheoryTy ℓ' tt}
  {C : String → TheoryTy ℓ'' tt}
  where
  ⊗ᴰ⊕-distL :
    ⊗ᴰ (A ⊕ B) (λ l _ → C l)
    ⊢ ⊗ᴰ A (λ l _ → C l) ⊕ ⊗ᴰ B (λ l _ → C l)
  ⊗ᴰ⊕-distL m (ms , e , (Sum.inl a , (c , _))) = Sum.inl (ms , e , (a , (c , tt*)))
  ⊗ᴰ⊕-distL m (ms , e , (Sum.inr b , (c , _))) = Sum.inr (ms , e , (b , (c , tt*)))

  ⊗ᴰ⊕-distL⁻ :
    ⊗ᴰ A (λ l _ → C l) ⊕ ⊗ᴰ B (λ l _ → C l)
    ⊢ ⊗ᴰ (A ⊕ B) (λ l _ → C l)
  ⊗ᴰ⊕-distL⁻ m (Sum.inl (ms , e , (a , (c , _)))) = ms , e , (Sum.inl a , (c , tt*))
  ⊗ᴰ⊕-distL⁻ m (Sum.inr (ms , e , (b , (c , _)))) = ms , e , (Sum.inr b , (c , tt*))

-- `ε` determines its yield too: the empty string.
module _ {C : String → TheoryTy ℓ tt} where
  ⊗ᴰ-ε : ⊗ᴰ εTy (λ l _ → C l) ⊢ εTy ⊗ C []
  ⊗ᴰ-ε m (ms , e , (u , (cont , _))) =
    ms , e , (u , (castEq {A = λ x → C x (ms (suc zero))}
                     (Eq.sym (u .snd .fst)) cont , tt*))

  ⊗ᴰ-ε⁻ : εTy ⊗ C [] ⊢ ⊗ᴰ εTy (λ l _ → C l)
  ⊗ᴰ-ε⁻ m (ms , e , (u , (cont , _))) =
    ms , e , (u , (castEq {A = λ x → C x (ms (suc zero))}
                     (u .snd .fst) cont , tt*))

-- A factor whose yield is determined collapses the index: at a literal the
-- continuation is needed at one string only.  This is why every leaf of a
-- regex costs nothing -- only a capture group actually indexes anything.
module _ {C : String → TheoryTy ℓ tt} (c : Alphabet) where
  ⊗ᴰ-lit : ⊗ᴰ ＂ c ＂ (λ l _ → C l) ⊢ ＂ c ＂ ⊗ C ⌈gen c ⌉
  ⊗ᴰ-lit m (ms , e , (p , (cont , _))) =
    ms , e , (p , (castEq {A = λ x → C x (ms (suc zero))} p cont , tt*))

  ⊗ᴰ-lit⁻ : ＂ c ＂ ⊗ C ⌈gen c ⌉ ⊢ ⊗ᴰ ＂ c ＂ (λ l _ → C l)
  ⊗ᴰ-lit⁻ m (ms , e , (p , (cont , _))) =
    ms , e , (p , (castEq {A = λ x → C x (ms (suc zero))} (Eq.sym p) cont , tt*))

-- The representable at a *known* string, as a `⊗`-chain: what a
-- backreference has to be parsed as, once the capture is in hand.
⌈⌉→ε : ⌈ [] ⌉ ⊢ εTy
⌈⌉→ε m p = (λ ()) , Eq.sym p , tt*

ε→⌈⌉ : εTy ⊢ ⌈ [] ⌉
ε→⌈⌉ m (ms , e , _) = Eq.sym e

module _ (c : Alphabet) (w : String) where
  ⌈⌉→⊗ : ⌈ c ∷ w ⌉ ⊢ ＂ c ＂ ⊗ ⌈ w ⌉
  ⌈⌉→⊗ m p = two (c ∷ []) w , Eq.sym p , (Eq.refl , (Eq.refl , tt*))

  ⊗→⌈⌉ : ＂ c ＂ ⊗ ⌈ w ⌉ ⊢ ⌈ c ∷ w ⌉
  ⊗→⌈⌉ m (ms , e , (p₀ , (p₁ , _))) =
    Eq.sym e Eq.∙ (Eq.ap (_++ ms (suc zero)) p₀ Eq.∙ Eq.ap ((c ∷ []) ++_) p₁)

-- The same collapse as `⊗ᴰ-lit`, at a whole known string: what a
-- backreference's own parser needs.
module _ {C : String → TheoryTy ℓ tt} (w : String) where
  ⊗ᴰ-⌈⌉ : ⊗ᴰ ⌈ w ⌉ (λ l _ → C l) ⊢ ⌈ w ⌉ ⊗ C w
  ⊗ᴰ-⌈⌉ m (ms , e , (p , (cont , _))) =
    ms , e , (p , (castEq {A = λ x → C x (ms (suc zero))} p cont , tt*))

  ⊗ᴰ-⌈⌉⁻ : ⌈ w ⌉ ⊗ C w ⊢ ⊗ᴰ ⌈ w ⌉ (λ l _ → C l)
  ⊗ᴰ-⌈⌉⁻ m (ms , e , (p , (cont , _))) =
    ms , e , (p , (castEq {A = λ x → C x (ms (suc zero))} (Eq.sym p) cont , tt*))

⊗ᴰ⊥-annihL : {C : String → TheoryTy ℓ tt} → ⊗ᴰ ⊥Ty (λ l _ → C l) ⊢ ⊥Ty
⊗ᴰ⊥-annihL m (ms , e , (b , _)) = b
