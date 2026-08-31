{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A character satisfying a decidable predicate.

   `⟨ c ⟩r` is one letter and `anyr` was all of them, with nothing in
   between -- so `[a-z]`, `[0-9]` and `[^"]` were inexpressible.  Finite
   disjunction does not rescue this: over `Bits 21` a complement class is
   two million disjuncts, and over an infinite alphabet it is not a finite
   disjunction at all.

   `satG P` is the sum of `literal c` over the letters `P` accepts.  It is
   `char` restricted along `P`, and everything about it is `char`'s proof
   with the index carrying its certificate. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Regex.Sat
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool ; true≢false)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.List using ([] ; _∷_)
import Cubical.Data.List.Properties as L
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
open import Cubical.Foundations.HLevels using (isSetΣ)

open import Theory.Instances.Monoid.Combinator.Decidable.Base Alphabet _≟_ ℓ
  public
open import Theory.Instances.Monoid.Precise Alphabet isSetAlphabet
  using (sat⊗-precise)
open import Theory.Instances.Monoid.Sat Alphabet isSetAlphabet public
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⊗⊕ᴰ-distL ; &⊕ᴰ-distR)

private variable ℓK : Level

dec-sat⊗↑ : {P : Alphabet → Bool} {K : TheoryTy ℓK tt}
  → satG P ⊗ DecTy K ⊢ DecTy (satG P ⊗ K)
dec-sat⊗↑ = ⊕-elim dec-yes (dec-no ∘⊢ sat⊗-precise) ∘⊢ ⊗⊕-distR

dec-sat⊗-at : (P : Alphabet → Bool) {K : TheorySet ℓK tt}
  → ty (▷ (DecSet K)) ⊢ DecTy (satG P ⊗ ty K)
dec-sat⊗-at P {K = K} = look⊗ br
  where
  -- no accepted letter sits at the front of a word of class `o`
  miss : (o : M₁) → ((x : Sat P) → o Eq.≡ tk (x .fst) → Empty.⊥)
       → ty (▷ (DecSet K)) & Λ₁ o ⊢ DecTy (satG P ⊗ ty K)
  miss o ne = dec-no ∘⊢ ⇒-intro (⊕ᴰ-elim dis ∘⊢ &⊕ᴰ-distR
    ∘⊢ ((π₂ ∘⊢ π₁) ,&p ⊗⊕ᴰ-distL) ∘⊢ (id⊢ ,& π₂))
    where
    dis : (x : Sat P) → Λ₁ o & (literal (x .fst) ⊗ ty K) ⊢ ⊥Ty
    dis x = Λ-disjoint o (tk (x .fst)) (ne x)
      ∘⊢ (id⊢ ,&p (id⊢ ,⊗ ⊤Ty-intro))

  br : (o : M₁) → ty (▷ (DecSet K)) & Λ₁ o ⊢ DecTy (satG P ⊗ ty K)
  br ε₁ = miss ε₁ λ _ ()
  br (tk d) = go (P d) refl
    where
    go : (b : Bool) → P d ≡ b
       → ty (▷ (DecSet K)) & Λ₁ (tk d) ⊢ DecTy (satG P ⊗ ty K)
    go true eq = dec-sat⊗↑ ∘⊢ (σ⊕ (d , eq) ,⊗ π₁) ∘⊢ ▷⊗r d
    go false eq = miss (tk d) λ where
      x Eq.refl → true≢false (sym (x .snd) ∙ eq)

satTok : {D : TheoryTy ℓK tt} (P : Alphabet → Bool) {ℓK' : Level}
  → D ⊢ Parser ℓK' ⟨▷⟩ ⟨□⟩ (satSet P)
satTok P = mkP λ K → ▷□ (dec-sat⊗-at P) ∘⊢ π₂
