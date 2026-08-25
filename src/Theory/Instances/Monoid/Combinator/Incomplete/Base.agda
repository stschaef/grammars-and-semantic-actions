-- Parser combinators inspired by agdarsec (Allais)
-- https://gallais.github.io/pdf/agdarsec18.pdf
-- These are total in the sense of Allais and intrinsically sound, but --
-- unlike `Combinator.Decidable` -- a failure is `nothing` rather than a
-- refutation, so a parser that gives up says nothing about the grammar.
-- This is the shape Allais and Danielsson actually use.
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

-- `Maybe` carries its set-ness, which is what a guarded recursion asks of a
-- grammar; this is `DecSet`'s counterpart.
MaybeSet : TheorySet ℓA tt → TheorySet ℓA tt
MaybeSet (A , sA) = Maybe A , isSetMaybe sA

fmapM : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} → A ⊢ B → Maybe A ⊢ Maybe B
fmapM = Monad.fmap MaybeMonad

-- The right strength of `Maybe` over `⊗`: a failure on the right factor is a
-- failure of the tensor.  This is where the incomplete parser is *cheaper*
-- than the decidable one -- no precision lemma is spent.
Maybe⊗r : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} → A ⊗ Maybe B ⊢ Maybe (A ⊗ B)
Maybe⊗r = ⊕-elim just (nothing ∘⊢ ⊤Ty-intro) ∘⊢ ⊗⊕-distR

-- The first branch that succeeds wins, so alternation needs no disjointness.
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

-- Reading `c` off the front: the guarded test is spent on the tail, and a
-- lookahead class other than `tk c` just fails.
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

-- The end of input, as a test: only the empty word is `ε`.
maybe-ε : ⊤Ty ⊢ Maybe εTy
maybe-ε = ⊕ᴰ-elim br ∘⊢ Λ-total
  where
  br : (o : M₁) → Λ₁ o ⊢ Maybe εTy
  br ε₁ = just ∘⊢ lowerTy
  br (tk c) = nothing ∘⊢ ⊤Ty-intro

ℓG : Level
ℓG = ℓ-max ℓM ℓ

ε↑Set : TheorySet ℓG tt
ε↑Set = LiftTheoryTy ℓ εTy , isSetLiftTheoryTy isSetεTy

-- A parser for A turns tests for a grammar K into tests for A ⊗ K
-- The two tags say which resources the domain and codomain refer to
-- ▷? ⟨▷⟩ A = ▷ A
-- ▷? ⟨□⟩ A = ▷ A & A ≅ □ A
Parser : ParserTag → ParserTag → TheorySet ℓA tt → TheoryTy _ tt
Parser a c A =
  &[ K ∈ TheorySet ℓG tt ]
    (ty (▷? a (MaybeSet K)) ⇒ ty (▷? c (MaybeSet (A ⊗Set K))))

ParserSet : (a c : ParserTag) → TheorySet ℓA tt → TheorySet _ tt
ParserSet a c A =
  Parser a c A , isSet&ᴰ λ K → isSet⇒ (▷? c (MaybeSet (A ⊗Set K)) .snd)

mkP : {a c : ParserTag} {A : TheorySet ℓA tt} {D : TheoryTy ℓD tt}
  → (∀ K → D & ty (▷? a (MaybeSet K)) ⊢ ty (▷? c (MaybeSet (A ⊗Set K))))
  → D ⊢ Parser a c A
mkP f = &ᴰ-intro λ K → ⇒-intro (f K)

pAt : {a c : ParserTag} {A : TheorySet ℓA tt} {D : TheoryTy ℓD tt}
  → D ⊢ Parser a c A → (K : TheorySet ℓG tt)
  → D & ty (▷? a (MaybeSet K)) ⊢ ty (▷? c (MaybeSet (A ⊗Set K)))
pAt p K = ⇒-app ∘⊢ ((π K ∘⊢ p) ,&p id⊢)

pmore : {c : ParserTag} {A : TheorySet ℓA tt} → Parser ⟨▷⟩ c A ⊢ Parser ⟨□⟩ c A
pmore = mkP λ K → pAt id⊢ K ∘⊢ (id& ▷wk)

pless : {a : ParserTag} {A : TheorySet ℓA tt} → Parser a ⟨□⟩ A ⊢ Parser a ⟨▷⟩ A
pless = mkP λ K → ▷wk ∘⊢ pAt id⊢ K

-- Only the forward map: nothing has to be said about the failures
mapP : {a c : ParserTag} {A : TheorySet ℓA tt} {B : TheorySet ℓB tt}
  → ty A ⊢ ty B → Parser a c A ⊢ Parser a c B
mapP f = mkP λ K → ▷maybe-map (f ,⊗ id⊢) ∘⊢ pAt id⊢ K

pApp : {A : TheorySet ℓA tt} (K : TheorySet ℓG tt)
  → ty (▷ (ParserSet ⟨□⟩ ⟨□⟩ A)) & ty (▷ (MaybeSet K))
  ⊢ ty (▷ (MaybeSet (A ⊗Set K)))
pApp K = ▷map (□here ∘⊢ pAt id⊢ K) ∘⊢ ▷lax ∘⊢ (id⊢ ,&p ▷δ□)

-- Combinators under an arbitray hypothesis D
module _ {D : TheoryTy ℓD tt} where

  infixr 15 _<|>_

  -- Sequencing of parsers
  seq : {a b c : ParserTag} {A : TheorySet ℓA tt} (B : TheorySet ℓG tt)
    → D ⊢ Parser b c A → D ⊢ Parser a b B
    → D ⊢ Parser a c (A ⊗Set B)
  seq B p q = mkP λ K →
    ▷maybe-map ⊗-assoc⁻ ∘⊢ pAt p (B ⊗Set K) ∘⊢ (π₁ ,& pAt q K)

  -- Alternation of parsers: biased, the left branch is preferred
  _<|>_ : {a c : ParserTag} {A : TheorySet ℓA tt} {B : TheorySet ℓB tt}
    → D ⊢ Parser a c A → D ⊢ Parser a c B → D ⊢ Parser a c (A ⊕Set B)
  (p <|> q) = mkP λ K →
    ▷maybe-map ⊗⊕-distL⁻ ∘⊢ ▷maybe-⊕& ∘⊢ (pAt p K ,& pAt q K)

  -- Parser for each literal
  tok : (c : Alphabet) → D ⊢ Parser ⟨▷⟩ ⟨□⟩ (litSet c)
  tok c = mkP λ K → ▷□ (maybe-lit⊗-at c) ∘⊢ π₂

  -- Parser for any literal
  anyTok : D ⊢ Parser ⟨▷⟩ ⟨□⟩ charSet
  anyTok = mkP λ K → ▷□ maybe-char⊗-at ∘⊢ π₂

  -- Parser for ε
  nil : D ⊢ Parser ⟨□⟩ ⟨□⟩ εSet
  nil = mkP λ K → ▷maybe-map ⊗ε-unit-l⁻ ∘⊢ π₂

  -- Parser that always fails
  fail : {a c : ParserTag} {A : TheorySet ℓA tt} → D ⊢ Parser a c A
  fail {c = c} = mkP λ K → ▷next {t = c} nothing

  -- a closed parser is available at every suffix
  box : {A : TheorySet ℓA tt} → ⊤Ty ⊢ Parser ⟨□⟩ ⟨□⟩ A
    → D ⊢ Parser ⟨▷⟩ ⟨▷⟩ A
  box p = mkP λ K → pApp K ∘⊢ (▷next {t = ⟨▷⟩} p ,&p id⊢)

□maybe-ε : {D : TheoryTy ℓD tt} → D ⊢ ty (□ (MaybeSet ε↑Set))
□maybe-ε = ▷next {t = ⟨□⟩} (fmapM liftTy ∘⊢ maybe-ε)

-- What a parser is observed at: a partial recognizer for A
Test : TheoryTy ℓA tt → Type _
Test A = ⊤Ty ⊢ Maybe A

-- A parser under the hypothesis ⊤ is sufficent for building a test for A
runP : {A : TheorySet ℓA tt} → ⊤Ty ⊢ Parser ⟨□⟩ ⟨□⟩ A → Test (ty A)
runP p =
  fmapM (⊗ε-unit-r ∘⊢ (id⊢ ,⊗ lowerTy))
  ∘⊢ □here ∘⊢ pAt p ε↑Set ∘⊢ (id⊢ ,& □maybe-ε)

-- Build parsers as fixpoints
module Fix {ℓA} (A : TheorySet ℓA tt) where

  -- Call the hypothetical parser on a strictly smaller suffix
  call : ty (▷ (ParserSet ⟨□⟩ ⟨□⟩ A)) ⊢ Parser ⟨▷⟩ ⟨▷⟩ A
  call = mkP pApp

  -- Guarded fixpoints build closed parsers
  fix : ty (▷ (ParserSet ⟨□⟩ ⟨□⟩ A)) ⊢ Parser ⟨□⟩ ⟨□⟩ A
    → ⊤Ty ⊢ Parser ⟨□⟩ ⟨□⟩ A
  fix = löbG {A = ParserSet ⟨□⟩ ⟨□⟩ A}

  test : ty (▷ (ParserSet ⟨□⟩ ⟨□⟩ A)) ⊢ Parser ⟨□⟩ ⟨□⟩ A → Test (ty A)
  test φ = runP (fix φ)
