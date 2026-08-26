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

open import Cubical.Data.Bool using (Bool ; true ; false ; _and_ ; _or_ ; true≢false)
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Combinator.Decidable.Star Alphabet _≟_ ℓ
  public
open import Theory.Instances.Monoid.KleeneStar.Guarded Alphabet isSetAlphabet
  public

-- `b` is "may match the empty word"
data RE : Bool → Type ℓAlph where
  εr   : RE true
  ⊥r   : RE false
  ⟨_⟩r : Alphabet → RE false
  anyr : RE false
  _⊗r_ : ∀ {b b'} → RE b → RE b' → RE (b and b')
  _⊕r_ : ∀ {b b'} → RE b → RE b' → RE (b or b')
  _*r  : RE false → RE true

infixr 20 _⊗r_
infixr 19 _⊕r_
infix 30 _*r
infix 30 ⟨_⟩r

-- one or more
_+r : RE false → RE false
r +r = r ⊗r (r *r)

infix 30 _+r

-- the level of the grammar a regex denotes
lv : ∀ {b} → RE b → Level
lv εr = ℓM
lv ⊥r = ℓ-zero
lv ⟨ c ⟩r = ℓM
lv anyr = ℓM
lv (r ⊗r r') = ℓ-max ℓAlph (ℓ-max (lv r) (lv r'))
lv (r ⊕r r') = ℓ-max (lv r) (lv r')
lv (r *r) = ℓF (lv r)

-- ...and the grammar itself, carrying its set-ness
⟦_⟧ : ∀ {b} (r : RE b) → TheorySet (lv r) tt
⟦ εr ⟧ = εSet
⟦ ⊥r ⟧ = ⊥Set
⟦ ⟨ c ⟩r ⟧ = litSet c
⟦ anyr ⟧ = charSet
⟦ r ⊗r r' ⟧ = ⟦ r ⟧ ⊗Set ⟦ r' ⟧
⟦ r ⊕r r' ⟧ = ⟦ r ⟧ ⊕Set ⟦ r' ⟧
⟦ r *r ⟧ = StarSet ⟦ r ⟧

------------------------------------------------------------------------
-- The parser, as a fold over the regex.
--
-- Two mutually-defined interpretations, one per hypothesis tag.  `parse▷`
-- exists only for non-nullable regexes -- that is what the `RE false`
-- index buys -- and it is what `many` demands of a star's body, so the
-- guardedness of the recursion is discharged by the typing rule.

parse  : ∀ {b} (r : RE b) (ℓK : Level)
       → ⊤Ty ⊢ Parser (ℓ-max ℓM ℓK) ⟨□⟩ ⟨□⟩ ⟦ r ⟧
-- the `b ≡ false` is threaded rather than matched: Agda cannot invert
-- `_and_` in an index, so the nullability equation travels as a proof
parse▷ : ∀ {b} (r : RE b) (ℓK : Level) → b ≡ false
       → ⊤Ty ⊢ Parser (ℓ-max ℓM ℓK) ⟨▷⟩ ⟨□⟩ ⟦ r ⟧

parse εr ℓK = nil
parse ⊥r ℓK = fail
parse ⟨ c ⟩r ℓK = pmore ∘⊢ tok c
parse anyr ℓK = pmore ∘⊢ anyTok
parse (r ⊗r r') ℓK = seq ⟦ r' ⟧ (parse r (ℓ⊗ (lv r') ℓK)) (parse r' ℓK)
parse (r ⊕r r') ℓK = parse r ℓK <|> parse r' ℓK
parse (r *r) ℓK = many ℓK ⟦ r ⟧ (parse▷ r (ℓ⊗ (ℓF (lv r)) ℓK) refl)

parse▷ εr ℓK p = Empty.rec (true≢false p)
parse▷ ⊥r ℓK p = fail
parse▷ ⟨ c ⟩r ℓK p = tok c
parse▷ anyr ℓK p = anyTok
parse▷ (_⊗r_ {false} {b'} r r') ℓK p =
  seq ⟦ r' ⟧ (parse▷ r (ℓ⊗ (lv r') ℓK) refl) (box (parse r' ℓK))
parse▷ (_⊗r_ {true} {false} r r') ℓK p =
  seq ⟦ r' ⟧ (parse r (ℓ⊗ (lv r') ℓK)) (parse▷ r' ℓK refl)
parse▷ (_⊗r_ {true} {true} r r') ℓK p = Empty.rec (true≢false p)
parse▷ (_⊕r_ {false} {false} r r') ℓK p =
  parse▷ r ℓK refl <|> parse▷ r' ℓK refl
parse▷ (_⊕r_ {false} {true} r r') ℓK p = Empty.rec (true≢false p)
parse▷ (_⊕r_ {true} {b'} r r') ℓK p = Empty.rec (true≢false p)
parse▷ (r *r) ℓK p = Empty.rec (true≢false p)

-- A regex, decided.
decide-r : ∀ {b} (r : RE b) (ℓK : Level) → Decidable (ty ⟦ r ⟧)
decide-r r ℓK = runP ℓK (parse r ℓK)

------------------------------------------------------------------------
-- The `RE false` index *is* the non-nullability witness: what the type
-- rules already forbid, the star fold no longer has to be told.

re-¬Nullable : ∀ {b} (r : RE b) → b ≡ false → ¬Nullable (ty ⟦ r ⟧)
re-¬Nullable εr p = Empty.rec (true≢false p)
re-¬Nullable ⊥r p = ⊥-¬Nullable
re-¬Nullable ⟨ c ⟩r p = literal-¬Nullable c
re-¬Nullable anyr p = char-¬Nullable
re-¬Nullable (_⊗r_ {false} {b'} r r') p =
  ⊗-¬Nullable (re-¬Nullable r refl)
re-¬Nullable (_⊗r_ {true} {false} r r') p =
  ⊗-¬NullableR (re-¬Nullable r' refl)
re-¬Nullable (_⊗r_ {true} {true} r r') p = Empty.rec (true≢false p)
re-¬Nullable (_⊕r_ {false} {false} r r') p =
  ⊕-¬Nullable (re-¬Nullable r refl) (re-¬Nullable r' refl)
re-¬Nullable (_⊕r_ {false} {true} r r') p = Empty.rec (true≢false p)
re-¬Nullable (_⊕r_ {true} {b'} r r') p = Empty.rec (true≢false p)
re-¬Nullable (r *r) p = Empty.rec (true≢false p)
