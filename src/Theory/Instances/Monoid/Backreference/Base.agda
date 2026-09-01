{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `⊗ᴰ A B`: `A ⊗ B` where the right factor may mention the string the left
   consumed.  `B l a = ⌈ l ⌉` is a backreference.  Nothing downstream of this
   file binds a model element. -}
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

-- `Dep`, `⊗ᴰ`, `⊗ᴰ-const` and `⊗ᴰ-assoc⁻` come from `Strings`.

-- `Strings.⊗-assoc` with the `C` slot re-indexed; the splits are identical.
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

⊗ᴰ-mapL : {A : TheoryTy ℓ tt} {B : TheoryTy ℓ' tt}
  {C : String → TheoryTy ℓ'' tt}
  → A ⊢ B → ⊗ᴰ A (λ l _ → C l) ⊢ ⊗ᴰ B (λ l _ → C l)
⊗ᴰ-mapL f m (ms , e , (a , (cont , _))) = ms , e , (f (ms zero) a , (cont , tt*))

-- the index sees only the string, so the summands' trees are never reconciled
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

module _ {C : String → TheoryTy ℓ tt} where
  ⊗ᴰ-ε : ⊗ᴰ εTy (λ l _ → C l) ⊢ εTy ⊗ C []
  ⊗ᴰ-ε m (ms , e , (u , (cont , _))) =
    ms , e , (u , (castEq {A = λ x → C x (ms (suc zero))}
                     (Eq.sym (u .snd .fst)) cont , tt*))

  ⊗ᴰ-ε⁻ : εTy ⊗ C [] ⊢ ⊗ᴰ εTy (λ l _ → C l)
  ⊗ᴰ-ε⁻ m (ms , e , (u , (cont , _))) =
    ms , e , (u , (castEq {A = λ x → C x (ms (suc zero))}
                     (u .snd .fst) cont , tt*))

-- Determined yield collapses the index: only a capture group indexes anything.
module _ {C : String → TheoryTy ℓ tt} (c : Alphabet) where
  ⊗ᴰ-lit : ⊗ᴰ ＂ c ＂ (λ l _ → C l) ⊢ ＂ c ＂ ⊗ C ⌈gen c ⌉
  ⊗ᴰ-lit m (ms , e , (p , (cont , _))) =
    ms , e , (p , (castEq {A = λ x → C x (ms (suc zero))} p cont , tt*))

  ⊗ᴰ-lit⁻ : ＂ c ＂ ⊗ C ⌈gen c ⌉ ⊢ ⊗ᴰ ＂ c ＂ (λ l _ → C l)
  ⊗ᴰ-lit⁻ m (ms , e , (p , (cont , _))) =
    ms , e , (p , (castEq {A = λ x → C x (ms (suc zero))} (Eq.sym p) cont , tt*))

-- `⌈ w ⌉` as a `⊗`-chain: how a backreference parses once the capture is in hand.
⌈⌉→ε : ⌈ [] ⌉ ⊢ εTy
⌈⌉→ε m p = (λ ()) , Eq.sym p , tt*

ε→⌈⌉ : εTy ⊢ ⌈ [] ⌉
ε→⌈⌉ m (ms , e , _) = Eq.sym e

module _ (c : Alphabet) (w : String) where
  ⌈⌉→⊗ : ⌈ c ∷ w ⌉ ⊢ ＂ c ＂ ⊗ ⌈ w ⌉
  ⌈⌉→⊗ = ⌈⌉-split (c ∷ []) w

  ⊗→⌈⌉ : ＂ c ＂ ⊗ ⌈ w ⌉ ⊢ ⌈ c ∷ w ⌉
  ⊗→⌈⌉ = ⌈⌉-cat (c ∷ []) w

-- the `⊗ᴰ-lit` collapse at a whole known string
module _ {C : String → TheoryTy ℓ tt} (w : String) where
  ⊗ᴰ-⌈⌉ : ⊗ᴰ ⌈ w ⌉ (λ l _ → C l) ⊢ ⌈ w ⌉ ⊗ C w
  ⊗ᴰ-⌈⌉ m (ms , e , (p , (cont , _))) =
    ms , e , (p , (castEq {A = λ x → C x (ms (suc zero))} p cont , tt*))

  ⊗ᴰ-⌈⌉⁻ : ⌈ w ⌉ ⊗ C w ⊢ ⊗ᴰ ⌈ w ⌉ (λ l _ → C l)
  ⊗ᴰ-⌈⌉⁻ m (ms , e , (p , (cont , _))) =
    ms , e , (p , (castEq {A = λ x → C x (ms (suc zero))} (Eq.sym p) cont , tt*))

⊗ᴰ⊥-annihL : {C : String → TheoryTy ℓ tt} → ⊗ᴰ ⊥Ty (λ l _ → C l) ⊢ ⊥Ty
⊗ᴰ⊥-annihL m (ms , e , (b , _)) = b
