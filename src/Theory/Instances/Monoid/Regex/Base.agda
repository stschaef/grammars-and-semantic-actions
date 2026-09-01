{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Regexes indexed by nullability: `(εr) *r` would loop, so star is only
   formed on a non-nullable body -- guardedness as a typing rule -- and
   the parser's hypothesis tag is read off the index (`⟨▷⟩` vs `⟨□⟩`). -}
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
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)



open import Theory.Instances.Monoid.Types Alphabet _≟_ hiding (isSetAlphabet)
open import Theory.Instances.Monoid.Types Alphabet _≟_ using (isSetAlphabet) public
open import Theory.Instances.Monoid.KleeneStar.Guarded Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⊗ε-unit-l⁻)
open import Theory.Instances.Monoid.Regex.Sat Alphabet _≟_ ℓ
  using (Sat ; satG ; satSet) public

open import Theory.Instances.Monoid.Regex.Nullability public

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

-- A regex with its nullability packaged; the pairing constructors are
-- deliberately not smart: eager ⊥-collapse would stick on variables.
RE? : Type ℓAlph
RE? = Σ[ n ∈ Nullability ] RE n

∅? ε? : RE?
∅? = notNullable , ⊥r
ε? = nullable , εr

infixr 20 _⊗?_
infixr 19 _⊕?_

_⊗?_ : RE? → RE? → RE?
(n , r) ⊗? (n' , r') = n ·ν n' , r ⊗r r'

_⊕?_ : RE? → RE? → RE?
(n , r) ⊕? (n' , r') = n +ν n' , r ⊕r r'

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

-- Other direction: the index really answers "does this regex match ε".
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
