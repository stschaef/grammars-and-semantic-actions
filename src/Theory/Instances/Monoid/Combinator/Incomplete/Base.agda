-- Parser combinators inspired by agdarsec (Allais)
-- https://gallais.github.io/pdf/agdarsec18.pdf
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Incomplete.Base
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Types Alphabet _≟_ public
open import Theory.Instances.Monoid.Suffix.Base Alphabet isSetAlphabet public
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⊗ε-unit-l⁻ ; ⊗ε-unit-r ; ⊗ε-unit-r⁻ ; &⊕ᴰ-distR)

private variable ℓA ℓB ℓC ℓD ℓK ℓL : Level

MaybeSet : TheorySet ℓA tt → TheorySet ℓA tt
MaybeSet (A , sA) = Maybe A , isSetMaybe sA

fmapM : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} → A ⊢ B → Maybe A ⊢ Maybe B
fmapM = Monad.fmap MaybeMonad

Maybe⊗r : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} → A ⊗ Maybe B ⊢ Maybe (A ⊗ B)
Maybe⊗r = ⊕-elim just (nothing ∘⊢ ⊤Ty-intro) ∘⊢ ⊗⊕-distR

maybe-⊕& : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → Maybe A & Maybe B ⊢ Maybe (A ⊕ B)
maybe-⊕& = orElse ∘⊢ (fmapM inl ,&p fmapM inr)

▷maybe-map : {t : ParserTag} {K : TheorySet ℓK tt} {L : TheorySet ℓL tt}
  → ty K ⊢ ty L → ty (▷? t (MaybeSet K)) ⊢ ty (▷? t (MaybeSet L))
▷maybe-map f = ▷map (fmapM f)

▷maybe-⊕& : {t : ParserTag} {K : TheorySet ℓK tt} {L : TheorySet ℓL tt}
  → ty (▷? t (MaybeSet K)) & ty (▷? t (MaybeSet L))
  ⊢ ty (▷? t (MaybeSet (K ⊕Set L)))
▷maybe-⊕& = ▷map maybe-⊕& ∘⊢ ▷lax

look⊗ : {K : TheorySet ℓK tt} {C : TheoryTy ℓC tt}
  → ((o : M₁) → ty (▷ (MaybeSet K)) & Λ₁ o ⊢ C) → ty (▷ (MaybeSet K)) ⊢ C
look⊗ br = ⊕ᴰ-elim br ∘⊢ &⊕ᴰ-distR ∘⊢ (id⊢ ,& (Λ-total ∘⊢ ⊤Ty-intro))

maybe-lit⊗-at : (c : Alphabet) {K : TheorySet ℓK tt}
  → ty (▷ (MaybeSet K)) ⊢ Maybe (literal c ⊗ ty K)
maybe-lit⊗-at c {K = K} = look⊗ br
  where
  br : (o : M₁) → ty (▷ (MaybeSet K)) & Λ₁ o ⊢ Maybe (literal c ⊗ ty K)
  br ε₁ = nothing ∘⊢ ⊤Ty-intro
  br (tk d) = go (d ≟ c)
    where
    go : (d Eq.≡ c) Sum.⊎ ((d Eq.≡ c) → Empty.⊥)
       → ty (▷ (MaybeSet K)) & Λ₁ (tk d) ⊢ Maybe (literal c ⊗ ty K)
    go (Sum.inl Eq.refl) = Maybe⊗r ∘⊢ (id⊢ ,⊗ π₁) ∘⊢ ▷⊗r c
    go (Sum.inr _) = nothing ∘⊢ ⊤Ty-intro

maybe-char⊗-at : {K : TheorySet ℓK tt}
  → ty (▷ (MaybeSet K)) ⊢ Maybe (char ⊗ ty K)
maybe-char⊗-at {K = K} = look⊗ br
  where
  br : (o : M₁) → ty (▷ (MaybeSet K)) & Λ₁ o ⊢ Maybe (char ⊗ ty K)
  br ε₁ = nothing ∘⊢ ⊤Ty-intro
  br (tk d) = Maybe⊗r ∘⊢ (σ⊕ d ,⊗ π₁) ∘⊢ ▷⊗r d

maybe-ε : ⊤Ty ⊢ Maybe εTy
maybe-ε = ⊕ᴰ-elim br ∘⊢ Λ-total
  where
  br : (o : M₁) → Λ₁ o ⊢ Maybe εTy
  br ε₁ = just ∘⊢ lowerTy
  br (tk c) = nothing ∘⊢ ⊤Ty-intro

ℓG : Level
ℓG = ℓ-max ℓM ℓ

ε↑Set : (ℓK : Level) → TheorySet (ℓ-max ℓM ℓK) tt
ε↑Set ℓK = LiftTheoryTy ℓK εTy , isSetLiftTheoryTy isSetεTy

ℓ⊗ : Level → Level → Level
ℓ⊗ ℓB ℓK = ℓ-max ℓAlph (ℓ-max ℓB ℓK)

-- A parser for A turns tests for a grammar K into tests for A ⊗ K
Parser : (ℓK : Level) → ParserTag → ParserTag → TheorySet ℓA tt → TheoryTy _ tt
Parser ℓK a c A =
  &[ K ∈ TheorySet ℓK tt ]
    (ty (▷? a (MaybeSet K)) ⇒ ty (▷? c (MaybeSet (A ⊗Set K))))

ParserSet : (ℓK : Level) (a c : ParserTag) → TheorySet ℓA tt → TheorySet _ tt
ParserSet ℓK a c A =
  Parser ℓK a c A , isSet&ᴰ λ K → isSet⇒ (▷? c (MaybeSet (A ⊗Set K)) .snd)

mkP : {ℓK : Level} {a c : ParserTag} {A : TheorySet ℓA tt} {D : TheoryTy ℓD tt}
  → (∀ (K : TheorySet ℓK tt)
      → D & ty (▷? a (MaybeSet K)) ⊢ ty (▷? c (MaybeSet (A ⊗Set K))))
  → D ⊢ Parser ℓK a c A
mkP f = &ᴰ-intro λ K → ⇒-intro (f K)

pAt : {ℓK : Level} {a c : ParserTag} {A : TheorySet ℓA tt} {D : TheoryTy ℓD tt}
  → D ⊢ Parser ℓK a c A → (K : TheorySet ℓK tt)
  → D & ty (▷? a (MaybeSet K)) ⊢ ty (▷? c (MaybeSet (A ⊗Set K)))
pAt p K = ⇒-app ∘⊢ ((π K ∘⊢ p) ,&p id⊢)

pmore : {ℓK : Level} {c : ParserTag} {A : TheorySet ℓA tt}
  → Parser ℓK ⟨▷⟩ c A ⊢ Parser ℓK ⟨□⟩ c A
pmore = mkP λ K → pAt id⊢ K ∘⊢ (id& ▷wk)

pless : {ℓK : Level} {a : ParserTag} {A : TheorySet ℓA tt}
  → Parser ℓK a ⟨□⟩ A ⊢ Parser ℓK a ⟨▷⟩ A
pless = mkP λ K → ▷wk ∘⊢ pAt id⊢ K

mapP : {ℓK : Level} {a c : ParserTag} {A : TheorySet ℓA tt} {B : TheorySet ℓB tt}
  → ty A ⊢ ty B → Parser ℓK a c A ⊢ Parser ℓK a c B
mapP f = mkP λ K → ▷maybe-map (f ,⊗ id⊢) ∘⊢ pAt id⊢ K

pApp : {ℓK : Level} {A : TheorySet ℓA tt} (K : TheorySet ℓK tt)
  → ty (▷ (ParserSet ℓK ⟨□⟩ ⟨□⟩ A)) & ty (▷ (MaybeSet K))
  ⊢ ty (▷ (MaybeSet (A ⊗Set K)))
pApp K = ▷map (□here ∘⊢ pAt id⊢ K) ∘⊢ ▷lax ∘⊢ (id⊢ ,&p ▷δ□)

-- Combinators under an arbitray hypothesis D
module _ {D : TheoryTy ℓD tt} where

  infixr 15 _<|>_

  seq : {ℓK ℓB : Level} {a b c : ParserTag} {A : TheorySet ℓA tt}
    (B : TheorySet ℓB tt)
    → D ⊢ Parser (ℓ⊗ ℓB ℓK) b c A → D ⊢ Parser ℓK a b B
    → D ⊢ Parser ℓK a c (A ⊗Set B)
  seq B p q = mkP λ K →
    ▷maybe-map ⊗-assoc⁻ ∘⊢ pAt p (B ⊗Set K) ∘⊢ (π₁ ,& pAt q K)

  _<|>_ : {ℓK : Level} {a c : ParserTag} {A : TheorySet ℓA tt} {B : TheorySet ℓB tt}
    → D ⊢ Parser ℓK a c A → D ⊢ Parser ℓK a c B
    → D ⊢ Parser ℓK a c (A ⊕Set B)
  (p <|> q) = mkP λ K →
    ▷maybe-map ⊗⊕-distL⁻ ∘⊢ ▷maybe-⊕& ∘⊢ (pAt p K ,& pAt q K)

  tok : {ℓK : Level} (c : Alphabet) → D ⊢ Parser ℓK ⟨▷⟩ ⟨□⟩ (litSet c)
  tok c = mkP λ K → ▷□ (maybe-lit⊗-at c) ∘⊢ π₂

  anyTok : {ℓK : Level} → D ⊢ Parser ℓK ⟨▷⟩ ⟨□⟩ charSet
  anyTok = mkP λ K → ▷□ maybe-char⊗-at ∘⊢ π₂

  nil : {ℓK : Level} → D ⊢ Parser ℓK ⟨□⟩ ⟨□⟩ εSet
  nil = mkP λ K → ▷maybe-map ⊗ε-unit-l⁻ ∘⊢ π₂

  fail : {ℓK : Level} {a c : ParserTag} {A : TheorySet ℓA tt}
    → D ⊢ Parser ℓK a c A
  fail {c = c} = mkP λ K → ▷next {t = c} nothing

  -- a closed parser is available at every suffix
  -- TODO rename
  box : {ℓK : Level} {A : TheorySet ℓA tt} → ⊤Ty ⊢ Parser ℓK ⟨□⟩ ⟨□⟩ A
    → D ⊢ Parser ℓK ⟨▷⟩ ⟨▷⟩ A
  box p = mkP λ K → pApp K ∘⊢ (▷next {t = ⟨▷⟩} p ,&p id⊢)

□maybe-ε : {ℓK : Level} {D : TheoryTy ℓD tt} → D ⊢ ty (□ (MaybeSet (ε↑Set ℓK)))
□maybe-ε = ▷next {t = ⟨□⟩} (fmapM liftTy ∘⊢ maybe-ε)

Test : TheoryTy ℓA tt → Type _
Test A = ⊤Ty ⊢ Maybe A

-- A parser under the hypothesis ⊤ is sufficent for building a test for A
runP : (ℓK : Level) {A : TheorySet ℓA tt}
  → ⊤Ty ⊢ Parser (ℓ-max ℓM ℓK) ⟨□⟩ ⟨□⟩ A → Test (ty A)
runP _ p =
  fmapM (⊗ε-unit-r ∘⊢ (id⊢ ,⊗ lowerTy))
  ∘⊢ □here ∘⊢ pAt p (ε↑Set _) ∘⊢ (id⊢ ,& □maybe-ε)

-- Build parsers as fixpoints
module Fix {ℓA} (ℓK : Level) (A : TheorySet ℓA tt) where

  -- TODO rename
  -- hate script variables
  ℓ𝒦 : Level
  ℓ𝒦 = ℓ-max ℓM ℓK

  -- Call the hypothetical parser on a strictly smaller suffix
  call : ty (▷ (ParserSet ℓ𝒦 ⟨□⟩ ⟨□⟩ A)) ⊢ Parser ℓ𝒦 ⟨▷⟩ ⟨▷⟩ A
  call = mkP pApp

  -- Guarded fixpoints build closed parsers
  fix : ty (▷ (ParserSet ℓ𝒦 ⟨□⟩ ⟨□⟩ A)) ⊢ Parser ℓ𝒦 ⟨□⟩ ⟨□⟩ A
    → ⊤Ty ⊢ Parser ℓ𝒦 ⟨□⟩ ⟨□⟩ A
  fix = löbG {A = ParserSet ℓ𝒦 ⟨□⟩ ⟨□⟩ A}

  -- ...which are then used to build tests
  test : ty (▷ (ParserSet ℓ𝒦 ⟨□⟩ ⟨□⟩ A)) ⊢ Parser ℓ𝒦 ⟨□⟩ ⟨□⟩ A
    → Test (ty A)
  test φ = runP ℓK (fix φ)
