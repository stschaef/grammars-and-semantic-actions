-- Parser combinators inspired by agdarsec (Allais)
-- https://gallais.github.io/pdf/agdarsec18.pdf
-- These are total in the sense of Allais, we also have the additional strengths
-- 1. Our type system ensures that these are intrinsically sound parsers
-- 2. We are further showing below that we may have intrinsic *completeness* too
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Decidable.Base
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Types Alphabet _≟_ public
open import Theory.Instances.Monoid.Precise Alphabet isSetAlphabet public
  using (dec-lit⊗↑ ; dec-char⊗↑)
open import Theory.Instances.Monoid.Suffix.Base Alphabet isSetAlphabet public
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⊗ε-unit-l⁻ ; ⊗ε-unit-r ; ⊗ε-unit-r⁻ ; ⊗⊕ᴰ-distL ; &⊕ᴰ-distR)

private variable ℓA ℓB ℓC ℓD ℓK ℓL : Level

▷dec-map : {t : ParserTag} {K : TheorySet ℓK tt} {L : TheorySet ℓL tt}
  → ty K ⊢ ty L → ty L ⊢ ty K
  → ty (▷? t (DecSet K)) ⊢ ty (▷? t (DecSet L))
▷dec-map f g = ▷map (dec-map f (¬Ty-map g))

▷dec-⊕& : {t : ParserTag} {K : TheorySet ℓK tt} {L : TheorySet ℓL tt}
  → ty (▷? t (DecSet K)) & ty (▷? t (DecSet L))
  ⊢ ty (▷? t (DecSet (K ⊕Set L)))
▷dec-⊕& = ▷map dec-⊕& ∘⊢ ▷lax

look⊗ : {K : TheorySet ℓK tt} {C : TheoryTy ℓC tt}
  → ((o : M₁) → ty (▷ (DecSet K)) & Λ₁ o ⊢ C) → ty (▷ (DecSet K)) ⊢ C
look⊗ br = ⊕ᴰ-elim br ∘⊢ &⊕ᴰ-distR ∘⊢ (id⊢ ,& (Λ-total ∘⊢ ⊤Ty-intro))

dec-lit⊗-at : (c : Alphabet) {K : TheorySet ℓK tt}
  → ty (▷ (DecSet K)) ⊢ DecTy (literal c ⊗ ty K)
dec-lit⊗-at c {K = K} = look⊗ br
  where
  ¬fibre : (o : M₁) → (o Eq.≡ tk c → Empty.⊥)
    → ty (▷ (DecSet K)) & Λ₁ o ⊢ DecTy (literal c ⊗ ty K)
  ¬fibre o ne = dec-no ∘⊢ ⇒-intro
    (Λ-disjoint o (tk c) ne
      ∘⊢ ((π₂ ∘⊢ π₁) ,& ((id⊢ ,⊗ ⊤Ty-intro) ∘⊢ π₂)))

  br : (o : M₁) → ty (▷ (DecSet K)) & Λ₁ o ⊢ DecTy (literal c ⊗ ty K)
  br ε₁ = ¬fibre ε₁ (λ ())
  br (tk d) = go (d ≟ c)
    where
    go : (d Eq.≡ c) Sum.⊎ ((d Eq.≡ c) → Empty.⊥)
       → ty (▷ (DecSet K)) & Λ₁ (tk d) ⊢ DecTy (literal c ⊗ ty K)
    go (Sum.inl Eq.refl) = dec-lit⊗↑ c ∘⊢ (id⊢ ,⊗ π₁) ∘⊢ ▷⊗r c
    go (Sum.inr ne) = ¬fibre (tk d) (λ where Eq.refl → ne Eq.refl)

dec-char⊗-at : {K : TheorySet ℓK tt}
  → ty (▷ (DecSet K)) ⊢ DecTy (char ⊗ ty K)
dec-char⊗-at {K = K} = look⊗ br
  where
  -- the empty word carries no letter, hence no `char`
  ε-char : Λ₁ ε₁ & (char ⊗ ty K) ⊢ ⊥Ty
  ε-char = ⊕ᴰ-elim dis ∘⊢ &⊕ᴰ-distR ∘⊢ (id⊢ ,&p ⊗⊕ᴰ-distL)
    where
    dis : (d : Alphabet) → Λ₁ ε₁ & (literal d ⊗ ty K) ⊢ ⊥Ty
    dis d = Λ-disjoint ε₁ (tk d) (λ ()) ∘⊢ (id⊢ ,&p (id⊢ ,⊗ ⊤Ty-intro))

  br : (o : M₁) → ty (▷ (DecSet K)) & Λ₁ o ⊢ DecTy (char ⊗ ty K)
  br ε₁ = dec-no ∘⊢ ⇒-intro (ε-char ∘⊢ ((π₂ ∘⊢ π₁) ,& π₂))
  br (tk d) = dec-char⊗↑ ∘⊢ (σ⊕ d ,⊗ π₁) ∘⊢ ▷⊗r d

ℓG : Level
ℓG = ℓ-max ℓM ℓ

ε↑Set : TheorySet ℓG tt
ε↑Set = LiftTheoryTy ℓ εTy , isSetLiftTheoryTy isSetεTy

-- A parser for A turns decisions on grammar K into
-- decisions on A ⊗ K
-- The two tags say which resources the domain and codomain refer to
-- ▷? ⟨▷⟩ A = ▷ A
-- ▷? ⟨□⟩ A = ▷ A & A ≅ □ A
Parser : ParserTag → ParserTag → TheorySet ℓA tt → TheoryTy _ tt
Parser a c A =
  &[ K ∈ TheorySet ℓG tt ]
    (ty (▷? a (DecSet K)) ⇒ ty (▷? c (DecSet (A ⊗Set K))))

ParserSet : (a c : ParserTag) → TheorySet ℓA tt → TheorySet _ tt
ParserSet a c A =
  Parser a c A , isSet&ᴰ λ K → isSet⇒ (▷? c (DecSet (A ⊗Set K)) .snd)

mkP : {a c : ParserTag} {A : TheorySet ℓA tt} {D : TheoryTy ℓD tt}
  → (∀ K → D & ty (▷? a (DecSet K)) ⊢ ty (▷? c (DecSet (A ⊗Set K))))
  → D ⊢ Parser a c A
mkP f = &ᴰ-intro λ K → ⇒-intro (f K)

pAt : {a c : ParserTag} {A : TheorySet ℓA tt} {D : TheoryTy ℓD tt}
  → D ⊢ Parser a c A → (K : TheorySet ℓG tt)
  → D & ty (▷? a (DecSet K)) ⊢ ty (▷? c (DecSet (A ⊗Set K)))
pAt p K = ⇒-app ∘⊢ ((π K ∘⊢ p) ,&p id⊢)

pmore : {c : ParserTag} {A : TheorySet ℓA tt} → Parser ⟨▷⟩ c A ⊢ Parser ⟨□⟩ c A
pmore = mkP λ K → pAt id⊢ K ∘⊢ (id& ▷wk)

pless : {a : ParserTag} {A : TheorySet ℓA tt} → Parser a ⟨□⟩ A ⊢ Parser a ⟨▷⟩ A
pless = mkP λ K → ▷wk ∘⊢ pAt id⊢ K

mapP : {a c : ParserTag} {A : TheorySet ℓA tt} {B : TheorySet ℓB tt}
  → ty A ⊢ ty B → ty B ⊢ ty A → Parser a c A ⊢ Parser a c B
mapP f g = mkP λ K → ▷dec-map (f ,⊗ id⊢) (g ,⊗ id⊢) ∘⊢ pAt id⊢ K

pApp : {A : TheorySet ℓA tt} (K : TheorySet ℓG tt)
  → ty (▷ (ParserSet ⟨□⟩ ⟨□⟩ A)) & ty (▷ (DecSet K))
  ⊢ ty (▷ (DecSet (A ⊗Set K)))
pApp K = ▷map (□here ∘⊢ pAt id⊢ K) ∘⊢ ▷lax ∘⊢ (id⊢ ,&p ▷δ□)

-- Combinators under an arbitray hypothesis D
module _ {D : TheoryTy ℓD tt} where

  infixr 15 _<|>_

  -- Sequencing of parsers
  seq : {a b c : ParserTag} {A : TheorySet ℓA tt} (B : TheorySet ℓG tt)
    → D ⊢ Parser b c A → D ⊢ Parser a b B
    → D ⊢ Parser a c (A ⊗Set B)
  seq B p q = mkP λ K →
    ▷dec-map ⊗-assoc⁻ ⊗-assoc ∘⊢ pAt p (B ⊗Set K) ∘⊢ (π₁ ,& pAt q K)

  -- Alternation of parsers
  _<|>_ : {a c : ParserTag} {A : TheorySet ℓA tt} {B : TheorySet ℓB tt}
    → D ⊢ Parser a c A → D ⊢ Parser a c B → D ⊢ Parser a c (A ⊕Set B)
  (p <|> q) = mkP λ K →
    ▷dec-map ⊗⊕-distL⁻ ⊗⊕-distL ∘⊢ ▷dec-⊕& ∘⊢ (pAt p K ,& pAt q K)

  -- Parser for each literal
  tok : (c : Alphabet) → D ⊢ Parser ⟨▷⟩ ⟨□⟩ (litSet c)
  tok c = mkP λ K → ▷□ (dec-lit⊗-at c) ∘⊢ π₂

  -- Parser for any literal
  anyTok : D ⊢ Parser ⟨▷⟩ ⟨□⟩ charSet
  anyTok = mkP λ K → ▷□ dec-char⊗-at ∘⊢ π₂

  -- Parser for ε
  nil : D ⊢ Parser ⟨□⟩ ⟨□⟩ εSet
  nil = mkP λ K → ▷dec-map ⊗ε-unit-l⁻ ⊗-unit-l ∘⊢ π₂

  -- Parser for ⊥
  fail : {a c : ParserTag} → D ⊢ Parser a c ⊥Set
  fail {c = c} = mkP λ K → ▷next {t = c} (dec-no ∘⊢ ⇒-intro (⊗⊥-annihL ∘⊢ π₂))

  -- a closed parser is available at every suffix
  box : {A : TheorySet ℓA tt} → ⊤Ty ⊢ Parser ⟨□⟩ ⟨□⟩ A
    → D ⊢ Parser ⟨▷⟩ ⟨▷⟩ A
  box p = mkP λ K → pApp K ∘⊢ (▷next {t = ⟨▷⟩} p ,&p id⊢)

□dec-ε : {D : TheoryTy ℓD tt} → D ⊢ ty (□ (DecSet ε↑Set))
□dec-ε = ▷next {t = ⟨□⟩} (decLiftTheoryTy dec-ε)

-- A parser under the hypothesis ⊤ is sufficent for
-- buidling a decider for A
runP : {A : TheorySet ℓA tt} → ⊤Ty ⊢ Parser ⟨□⟩ ⟨□⟩ A → Decidable (ty A)
runP p =
  dec-map (⊗ε-unit-r ∘⊢ (id⊢ ,⊗ lowerTy))
          (¬Ty-map ((id⊢ ,⊗ liftTy) ∘⊢ ⊗ε-unit-r⁻))
  ∘⊢ □here ∘⊢ pAt p ε↑Set ∘⊢ (id⊢ ,& □dec-ε)

-- Build parsers as fixpoints
module Fix {ℓA} (A : TheorySet ℓA tt) where

  -- Call the hypothetical parser on a strictly smaller suffix
  call : ty (▷ (ParserSet ⟨□⟩ ⟨□⟩ A)) ⊢ Parser ⟨▷⟩ ⟨▷⟩ A
  call = mkP pApp

  -- Guarded fixpoints build closed parsers
  fix : ty (▷ (ParserSet ⟨□⟩ ⟨□⟩ A)) ⊢ Parser ⟨□⟩ ⟨□⟩ A
    → ⊤Ty ⊢ Parser ⟨□⟩ ⟨□⟩ A
  fix = löbG {A = ParserSet ⟨□⟩ ⟨□⟩ A}

  -- ...which are then used to build deciders
  decide : ty (▷ (ParserSet ⟨□⟩ ⟨□⟩ A)) ⊢ Parser ⟨□⟩ ⟨□⟩ A
    → Decidable (ty A)
  decide φ = runP (fix φ)
