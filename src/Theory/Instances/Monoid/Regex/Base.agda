{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Regular expressions indexed by nullability.

   `RegularExpression` lets you write `(εr) *r`, whose parser would loop.
   Here nullability is an index, so a star can only be formed on a
   non-nullable body -- the guardedness side condition becomes a typing
   rule rather than a lemma -- and the parser's hypothesis tag is read off
   the index: `⟨▷⟩` for a regex that must consume, `⟨□⟩` for one that
   need not. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Regex.Base
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Unit using (Unit)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)

open import Theory.Instances.Monoid.Combinator.Decidable.Star Alphabet _≟_ ℓ
  public
open import Theory.Instances.Monoid.KleeneStar.Guarded Alphabet isSetAlphabet
  public
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⊗ε-unit-l⁻)
open import Theory.Instances.Monoid.Regex.Sat Alphabet _≟_ ℓ
  using (Sat ; satG ; satSet ; satTok) public

-- Whether a regex may match the empty word.  A `Bool` here would say
-- nothing about which of the two truth values means what, and the
-- operations below would be `_and_`/`_or_` with the same ambiguity.
data Nullability : Type ℓ-zero where
  nullable notNullable : Nullability

ν≢ν̸ : nullable ≡ notNullable → Empty.⊥
ν≢ν̸ p = subst Discern p _
  where
  Discern : Nullability → Type ℓ-zero
  Discern nullable = Unit
  Discern notNullable = Empty.⊥

-- concatenation is nullable only if both sides are; alternation if either
-- is.  Both are stated so the *left* argument drives, which is what keeps
-- the indices reducing under a variable right argument.
_·ν_ : Nullability → Nullability → Nullability
notNullable ·ν _ = notNullable
nullable ·ν y = y

_+ν_ : Nullability → Nullability → Nullability
nullable +ν _ = nullable
notNullable +ν y = y

data RE : Nullability → Type ℓAlph where
  εr   : RE nullable
  ⊥r   : RE notNullable
  ⟨_⟩r : Alphabet → RE notNullable
  satr : (Alphabet → Bool) → RE notNullable
  _⊗r_ : ∀ {n n'} → RE n → RE n' → RE (n ·ν n')
  _⊕r_ : ∀ {n n'} → RE n → RE n' → RE (n +ν n')
  _*r  : RE notNullable → RE nullable

infixr 20 _⊗r_
infixr 19 _⊕r_
infix 30 _*r
infix 30 ⟨_⟩r

anyr : RE notNullable
anyr = satr λ _ → true

_+r : RE notNullable → RE notNullable
r +r = r ⊗r (r *r)

infix 30 _+r

lv : ∀ {n} → RE n → Level
lv εr = ℓM
lv ⊥r = ℓ-zero
lv ⟨ c ⟩r = ℓM
lv (satr P) = ℓM
lv (r ⊗r r') = ℓ-max ℓAlph (ℓ-max (lv r) (lv r'))
lv (r ⊕r r') = ℓ-max (lv r) (lv r')
lv (r *r) = ℓF (lv r)

⟦_⟧ : ∀ {n} (r : RE n) → TheorySet (lv r) tt
⟦ εr ⟧ = εSet
⟦ ⊥r ⟧ = ⊥Set
⟦ ⟨ c ⟩r ⟧ = litSet c
⟦ satr P ⟧ = satSet P
⟦ r ⊗r r' ⟧ = ⟦ r ⟧ ⊗Set ⟦ r' ⟧
⟦ r ⊕r r' ⟧ = ⟦ r ⟧ ⊕Set ⟦ r' ⟧
⟦ r *r ⟧ = StarSet ⟦ r ⟧

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

sat-¬Nullable : {P : Alphabet → Bool} → ¬Nullable (satG P)
sat-¬Nullable m ((x , lc) , eps) = literal-¬Nullable (x .fst) m (lc , eps)

re-¬Nullable : ∀ {n} (r : RE n) → n ≡ notNullable → ¬Nullable (ty ⟦ r ⟧)
re-¬Nullable εr p = Empty.rec (ν≢ν̸ p)
re-¬Nullable ⊥r p = ⊥-¬Nullable
re-¬Nullable ⟨ c ⟩r p = literal-¬Nullable c
re-¬Nullable (satr P) p = sat-¬Nullable
re-¬Nullable (_⊗r_ {notNullable} {n'} r r') p =
  ⊗-¬Nullable (re-¬Nullable r refl)
re-¬Nullable (_⊗r_ {nullable} {notNullable} r r') p =
  ⊗-¬NullableR (re-¬Nullable r' refl)
re-¬Nullable (_⊗r_ {nullable} {nullable} r r') p = Empty.rec (ν≢ν̸ p)
re-¬Nullable (_⊕r_ {notNullable} {notNullable} r r') p =
  ⊕-¬Nullable (re-¬Nullable r refl) (re-¬Nullable r' refl)
re-¬Nullable (_⊕r_ {notNullable} {nullable} r r') p = Empty.rec (ν≢ν̸ p)
re-¬Nullable (_⊕r_ {nullable} {n'} r r') p = Empty.rec (ν≢ν̸ p)
re-¬Nullable (r *r) p = Empty.rec (ν≢ν̸ p)

-- Nullability is decided, and the index is what decides it.
--
-- `re-¬Nullable` above gives one direction.  With the other, the syntactic
-- index is not bookkeeping: it answers the semantic question "does this
-- regex match the empty word", correctly, for every regex.

re-Nullable : ∀ {n} (r : RE n) → n ≡ nullable → εTy ⊢ ty ⟦ r ⟧
re-Nullable εr p = id⊢
re-Nullable ⊥r p = Empty.rec (ν≢ν̸ (sym p))
re-Nullable ⟨ c ⟩r p = Empty.rec (ν≢ν̸ (sym p))
re-Nullable (satr P) p = Empty.rec (ν≢ν̸ (sym p))
re-Nullable (_⊗r_ {nullable} {nullable} r r') p =
  (re-Nullable r refl ,⊗ re-Nullable r' refl) ∘⊢ ⊗ε-unit-l⁻
re-Nullable (_⊗r_ {nullable} {notNullable} r r') p = Empty.rec (ν≢ν̸ (sym p))
re-Nullable (_⊗r_ {notNullable} {n'} r r') p = Empty.rec (ν≢ν̸ (sym p))
re-Nullable (_⊕r_ {nullable} {n'} r r') p = inl ∘⊢ re-Nullable r refl
re-Nullable (_⊕r_ {notNullable} {nullable} r r') p = inr ∘⊢ re-Nullable r' refl
re-Nullable (_⊕r_ {notNullable} {notNullable} r r') p = Empty.rec (ν≢ν̸ (sym p))
re-Nullable (r *r) p = roll↑ ∘⊢ inr

-- ...so the two together are a decision, with no case left open.
decNullable : ∀ {n} (r : RE n)
  → (εTy ⊢ ty ⟦ r ⟧) Sum.⊎ ¬Nullable (ty ⟦ r ⟧)
decNullable {nullable} r = Sum.inl (re-Nullable r refl)
decNullable {notNullable} r = Sum.inr (re-¬Nullable r refl)
