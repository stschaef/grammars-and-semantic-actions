{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Repetition, as a parser.  `KleeneStar` has the grammar; this is the
   fixpoint that parses into it.

   `many` cannot be given a nullable element parser: `seq` puts it in the
   guarded slot, and `nil : Parser ⟨□⟩ ⟨□⟩` has no `⟨▷⟩` codomain to go
   there.  agdarsec carries that as a side condition; here it is a type
   error.

   `A *` sits at `ℓF ℓA`, a universe above its element, and that is fine:
   `seq` is polymorphic in its continuation's level, so the star is a legal
   continuation wherever it lands.  The element parser is asked for at
   `ℓ⊗ (ℓF ℓA) ℓ𝒦`, which is why `tok`/`anyTok` are level-polymorphic. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Decidable.Star
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Combinator.Decidable.Base Alphabet _≟_ ℓ public
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet public

private variable ℓA ℓB ℓD ℓK : Level

StarSet : (A : TheorySet ℓA tt) → TheorySet (ℓF ℓA) tt
StarSet (A , sA) = A * , isSetStar sA

-- `roll*` against the parser's `εSet` rather than the code's lifted one
roll↑ : {A : TheoryTy ℓA tt} → (A ⊗ (A *)) ⊕ εTy ⊢ A *
roll↑ = roll* ∘⊢ ⊕-elim inl (inr ∘⊢ liftTy)

unroll↑ : {A : TheoryTy ℓA tt} → A * ⊢ (A ⊗ (A *)) ⊕ εTy
unroll↑ = ⊕-elim inl (inr ∘⊢ lowerTy) ∘⊢ unroll*

module _ (ℓK : Level) (A : TheorySet ℓA tt) where
  private
    module P = Fix ℓK (StarSet A)

    ℓE : Level
    ℓE = ℓ⊗ (ℓF ℓA) P.ℓ𝒦

  -- `A *`, right-nested.  A closed parser is available under any
  -- hypothesis, `⊤Ty` being terminal, so `p` needs no rank-2 type.
  many : ⊤Ty ⊢ Parser ℓE ⟨▷⟩ ⟨□⟩ A
       → ⊤Ty ⊢ Parser P.ℓ𝒦 ⟨□⟩ ⟨□⟩ (StarSet A)
  many p = P.fix
    (mapP roll↑ unroll↑ ∘⊢ ((pmore ∘⊢ seq (StarSet A) (p ∘⊢ ⊤Ty-intro) P.call) <|> nil))

  -- `A ⁺`
  some : ⊤Ty ⊢ Parser ℓE ⟨▷⟩ ⟨□⟩ A
       → ⊤Ty ⊢ Parser P.ℓ𝒦 ⟨▷⟩ ⟨□⟩ (A ⊗Set StarSet A)
  some p = seq (StarSet A) p (box (many p))

-- `p (s p)*`.  The element parsers are used at several continuation levels
-- (once for the pair, once inside the star), so here the rank-2 level
-- quantification is real -- unlike quantifying over the hypothesis, which
-- `⊤Ty` being terminal makes free.
sepBy : (ℓK : Level) {A : TheorySet ℓA tt} {S : TheorySet ℓB tt}
  → (∀ {ℓ'} → ⊤Ty ⊢ Parser ℓ' ⟨▷⟩ ⟨□⟩ A)
  → (∀ {ℓ'} → ⊤Ty ⊢ Parser ℓ' ⟨▷⟩ ⟨□⟩ S)
  → ⊤Ty ⊢ Parser (ℓ-max ℓM ℓK) ⟨▷⟩ ⟨□⟩
      (A ⊗Set StarSet (S ⊗Set A))
sepBy ℓK {A = A} {S = S} p s =
  seq (StarSet (S ⊗Set A)) p (box (many ℓK (S ⊗Set A) (seq A s (pless ∘⊢ p))))

module _ {D : TheoryTy ℓD tt} where

  -- `p?`
  option : {ℓK : Level} {A : TheorySet ℓA tt}
    → D ⊢ Parser ℓK ⟨▷⟩ ⟨□⟩ A
    → D ⊢ Parser ℓK ⟨□⟩ ⟨□⟩ (A ⊕Set εSet)
  option p = (pmore ∘⊢ p) <|> nil

  -- `l p r`
  between : {ℓK : Level} {a b c : ParserTag} {L : TheorySet ℓA tt} {A : TheorySet ℓB tt}
    {R : TheorySet ℓD tt}
    → D ⊢ Parser (ℓ⊗ ℓB (ℓ⊗ ℓD ℓK)) b c L
    → D ⊢ Parser (ℓ⊗ ℓD ℓK) a b A → D ⊢ Parser ℓK ⟨▷⟩ a R
    → D ⊢ Parser ℓK ⟨▷⟩ c ((L ⊗Set A) ⊗Set R)
  between {A = A} {R = R} l p r = seq R (seq A l p) r
