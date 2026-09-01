{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The decidable parser for `RE`: nullability reads off the hypothesis
   tag, so a star body gets `⟨▷⟩` and everything else `⟨□⟩`. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Regex.Decide
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Combinator.Decidable.Star Alphabet _≟_ ℓ
open import Theory.Instances.Monoid.Regex.Base Alphabet _≟_ ℓ hiding (isSetAlphabet)
open import Theory.Instances.Monoid.Precise Alphabet isSetAlphabet
  using (sat⊗-precise)
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⊗⊕ᴰ-distL)

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

parse  : ∀ {n} (r : RE n) (ℓK : Level)
       → ⊤Ty ⊢ Parser (ℓ-max ℓM ℓK) ⟨□⟩ ⟨□⟩ ⟦ r ⟧
-- the equation is threaded rather than matched: Agda cannot invert
-- `_·ν_` in an index
parse▷ : ∀ {n} (r : RE n) (ℓK : Level) → n ≡ notNullable
       → ⊤Ty ⊢ Parser (ℓ-max ℓM ℓK) ⟨▷⟩ ⟨□⟩ ⟦ r ⟧

parse εr ℓK = nil
parse ⊥r ℓK = fail
parse ⟨ c ⟩r ℓK = pmore ∘⊢ tok c
parse (satr P) ℓK = pmore ∘⊢ satTok P
parse (r ⊗r r') ℓK = seq ⟦ r' ⟧ (parse r (ℓ⊗ (lv r') ℓK)) (parse r' ℓK)
parse (r ⊕r r') ℓK = parse r ℓK <|> parse r' ℓK
parse (r *r) ℓK = many ℓK ⟦ r ⟧ (parse▷ r (ℓ⊗ (ℓF (lv r)) ℓK) refl)

parse▷ εr ℓK p = Empty.rec (ν≢ν̸ p)
parse▷ ⊥r ℓK p = fail
parse▷ ⟨ c ⟩r ℓK p = tok c
parse▷ (satr P) ℓK p = satTok P
parse▷ (_⊗r_ {notNullable} {n'} r r') ℓK p =
  seq ⟦ r' ⟧ (parse▷ r (ℓ⊗ (lv r') ℓK) refl) (box (parse r' ℓK))
parse▷ (_⊗r_ {nullable} {notNullable} r r') ℓK p =
  seq ⟦ r' ⟧ (parse r (ℓ⊗ (lv r') ℓK)) (parse▷ r' ℓK refl)
parse▷ (_⊗r_ {nullable} {nullable} r r') ℓK p = Empty.rec (ν≢ν̸ p)
parse▷ (_⊕r_ {notNullable} {notNullable} r r') ℓK p =
  parse▷ r ℓK refl <|> parse▷ r' ℓK refl
parse▷ (_⊕r_ {notNullable} {nullable} r r') ℓK p = Empty.rec (ν≢ν̸ p)
parse▷ (_⊕r_ {nullable} {n'} r r') ℓK p = Empty.rec (ν≢ν̸ p)
parse▷ (r *r) ℓK p = Empty.rec (ν≢ν̸ p)

decide-r : ∀ {n} (r : RE n) (ℓK : Level) → Decidable (ty ⟦ r ⟧)
decide-r r ℓK = runP ℓK (parse r ℓK)
