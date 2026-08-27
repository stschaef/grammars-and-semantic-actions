-- Parser combinators inspired by agdarsec (Allais)
-- https://gallais.github.io/pdf/agdarsec18.pdf
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The combinators, once, over the functor that says what an answer is.

   `Decidable`, `Incomplete` and `NonDet` were three copies differing only
   in `Ans`.  What the combinators ask of it is not a monad -- `bind` is
   never used -- but `AnswerFunctor`: an action on *isomorphisms*, a
   choice, two token rules, and an answer at `ε`.  Isomorphisms rather
   than maps because a combinator only ever transports an answer along
   the monoidal structure; variance is where the three instances differ,
   so it belongs in their `mapP`.  `mapP` and `fail` are therefore in
   `CovariantAnswer`, not here -- one cannot refuse to decide.

   `LawfulAnswer` adds the functor laws separately, since `AnswerFunctor`
   constrains types and not behaviour, and sketching a new answer should
   not owe the proofs up front. -}
open import Cubical.Foundations.Prelude
open import Cubical.WildCat.LocallySmall.Base
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Core
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  where

open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
open import Cubical.Foundations.HLevels using (isSetΠ)

open import Theory.Instances.Monoid.Types Alphabet _≟_ public
open import Theory.Instances.Monoid.Suffix.Base Alphabet isSetAlphabet public
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⊗ε-unit-l⁻ ; ⊗ε-unit-r ; ⊗ε-unit-r⁻ ; &⊕ᴰ-distR)
open import Theory.Instances.Monoid.Unitor Alphabet isSetAlphabet
  using (⊗-assoc⁻∘⊗-assoc ; ⊗-assoc∘⊗-assoc⁻
        ; ⊗-unit-l∘l⁻ ; ⊗-unit-l⁻∘l ; ⊗-unit-r∘r⁻ ; ⊗-unit-r⁻∘r ; ⊗≅)

private variable ℓA ℓB ℓC ℓD ℓK ℓL : Level

ℓ⊗ : Level → Level → Level
ℓ⊗ ℓB ℓK = ℓ-max ℓAlph (ℓ-max ℓB ℓK)

ε↑Set : (ℓK : Level) → TheorySet (ℓ-max ℓM ℓK) tt
ε↑Set ℓK = LiftTheoryTy ℓK εTy , isSetLiftTheoryTy isSetεTy

-- Splitting on the lookahead class of the current string.  Independent of
-- what an answer is; the three token rules are all built from it.
look⊗ : {A : TheorySet ℓA tt} {C : TheoryTy ℓC tt}
  → ((o : M₁) → ty (▷ A) & Λ₁ o ⊢ C) → ty (▷ A) ⊢ C
look⊗ br = ⊕ᴰ-elim br ∘⊢ &⊕ᴰ-distR ∘⊢ (id⊢ ,& (Λ-total ∘⊢ ⊤Ty-intro))

-- The five isomorphisms the combinators transport along.  `Unitor` and
-- `Types` prove the round trips; these only bundle them.

open WildCatNotation
open WildCatIso

module _ {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt} where
  ⊗-assoc≅ : (A ⊗ (B ⊗ C)) ≅ ((A ⊗ B) ⊗ C)
  ⊗-assoc≅ .fun = ⊗-assoc⁻
  ⊗-assoc≅ .inv = ⊗-assoc
  ⊗-assoc≅ .sec = ⊗-assoc⁻∘⊗-assoc
  ⊗-assoc≅ .ret = ⊗-assoc∘⊗-assoc⁻

  ⊗⊕-distL≅ : ((A ⊗ C) ⊕ (B ⊗ C)) ≅ ((A ⊕ B) ⊗ C)
  ⊗⊕-distL≅ .fun = ⊗⊕-distL⁻
  ⊗⊕-distL≅ .inv = ⊗⊕-distL
  ⊗⊕-distL≅ .sec = ⊗⊕-distL⁻∘distL
  ⊗⊕-distL≅ .ret = ⊗⊕-distL∘distL⁻

-- Isomorphisms of grammars compose and invert.  The wildcat has these, but
-- the grammar `≅` is a private module application there, so they are
-- re-bundled at the concrete type.
inv≅ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} → A ≅ B → B ≅ A
inv≅ φ .fun = φ .inv
inv≅ φ .inv = φ .fun
inv≅ φ .sec = φ .ret
inv≅ φ .ret = φ .sec

infixr 9 _⋆≅_
_⋆≅_ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → A ≅ B → B ≅ C → A ≅ C
(φ ⋆≅ ψ) .fun = ψ .fun ∘⊢ φ .fun
(φ ⋆≅ ψ) .inv = φ .inv ∘⊢ ψ .inv
(φ ⋆≅ ψ) .sec = cong (λ z → ψ .fun ∘⊢ z ∘⊢ ψ .inv) (φ .sec) ∙ ψ .sec
(φ ⋆≅ ψ) .ret = cong (λ z → φ .inv ∘⊢ z ∘⊢ φ .fun) (ψ .ret) ∙ φ .ret

-- A `⊢`-term into a `TheorySet` is a set, so an isomorphism is determined by
-- its two maps: the round-trip fields are propositions.
isSet⊢ : {A : TheoryTy ℓA tt} {B : TheorySet ℓB tt} → isSet (A ⊢ ty B)
isSet⊢ {B = B} = isSetΠ λ m → isSetΠ λ _ → B .snd m

≅≡ : {A B : TheorySet ℓA tt} {φ ψ : ty A ≅ ty B}
  → φ .fun ≡ ψ .fun → φ .inv ≡ ψ .inv → φ ≡ ψ
≅≡ {φ = φ} {ψ = ψ} p q i .fun = p i
≅≡ {φ = φ} {ψ = ψ} p q i .inv = q i
≅≡ {B = B} {φ = φ} {ψ = ψ} p q i .sec =
  isProp→PathP (λ j → isSet⊢ {B = B} (q j ⋆⊢ p j) id⊢) (φ .sec) (ψ .sec) i
≅≡ {A = A} {φ = φ} {ψ = ψ} p q i .ret =
  isProp→PathP (λ j → isSet⊢ {B = A} (p j ⋆⊢ q j) id⊢) (φ .ret) (ψ .ret) i

id≅ : {A : TheoryTy ℓA tt} → A ≅ A
id≅ .fun = id⊢
id≅ .inv = id⊢
id≅ .sec = refl
id≅ .ret = refl

module _ {A : TheoryTy ℓA tt} where
  ⊗ε-unit-l≅ : A ≅ (εTy ⊗ A)
  ⊗ε-unit-l≅ .fun = ⊗ε-unit-l⁻
  ⊗ε-unit-l≅ .inv = ⊗-unit-l
  ⊗ε-unit-l≅ .sec = ⊗-unit-l⁻∘l
  ⊗ε-unit-l≅ .ret = ⊗-unit-l∘l⁻

  -- `Lift` has η, so both round trips are `refl`.
  lift≅ : A ≅ LiftTheoryTy ℓB A
  lift≅ .fun = liftTy
  lift≅ .inv = lowerTy
  lift≅ .sec = refl
  lift≅ .ret = refl

  -- the unit on the right, at the lifted `ε` a continuation carries
  ⊗ε↑-unit-r≅ : (A ⊗ LiftTheoryTy ℓB εTy) ≅ A
  ⊗ε↑-unit-r≅ .fun = ⊗ε-unit-r ∘⊢ (id⊢ ,⊗ lowerTy)
  ⊗ε↑-unit-r≅ .inv = (id⊢ ,⊗ liftTy) ∘⊢ ⊗ε-unit-r⁻
  ⊗ε↑-unit-r≅ .sec = ⊗-unit-r∘r⁻
  ⊗ε↑-unit-r≅ .ret =
    cong (λ z → (id⊢ ,⊗ liftTy) ∘⊢ z ∘⊢ (id⊢ ,⊗ lowerTy)) ⊗-unit-r⁻∘r


record AnswerFunctor : Typeω where
  field
    ℓAns : Level → Level
    Ans : {ℓA : Level} → TheorySet ℓA tt → TheorySet (ℓAns ℓA) tt

    -- the action on isomorphisms.  `Dec` needs the backward map to move a
    -- refutation and `Maybe`/`ND` ignore it, but no combinator here ever
    -- has two independent maps to give: it always has one isomorphism.
    Ans-≅ : {ℓA ℓB : Level} {A : TheorySet ℓA tt} {B : TheorySet ℓB tt}
      → ty A ≅ ty B → ty (Ans A) ⊢ ty (Ans B)

    Ans-⊕& : {ℓA ℓB : Level} {A : TheorySet ℓA tt} {B : TheorySet ℓB tt}
      → ty (Ans A) & ty (Ans B) ⊢ ty (Ans (A ⊕Set B))

    Ans-lit : {ℓK : Level} (c : Alphabet) {K : TheorySet ℓK tt}
      → ty (▷ (Ans K)) ⊢ ty (Ans (litSet c ⊗Set K))

    Ans-any : {ℓK : Level} {K : TheorySet ℓK tt}
      → ty (▷ (Ans K)) ⊢ ty (Ans (charSet ⊗Set K))

    Ans-ε : ⊤Ty ⊢ ty (Ans εSet)

-- A covariant answer additionally has a plain `fmap` and an empty answer.
-- `Dec` has neither: transporting a refutation needs the backward map, and
-- `⊤Ty ⊢ DecTy A` at an arbitrary `A` is a decision procedure, not a
-- default.
record CovariantAnswer (𝒯 : AnswerFunctor) : Typeω where
  open AnswerFunctor 𝒯
  field
    Ans-map : {ℓA ℓB : Level} {A : TheorySet ℓA tt} {B : TheorySet ℓB tt}
      → ty A ⊢ ty B → ty (Ans A) ⊢ ty (Ans B)
    Ans-empty : {ℓA : Level} {A : TheorySet ℓA tt} → ⊤Ty ⊢ ty (Ans A)

-- A divariant answer transports along a pair of maps that need not be
-- inverse.  Nothing in `Core` or `Syntax` needs it -- the grammars' own
-- `roll`/`unroll` pairs are proved to be isomorphisms, so they go through
-- `mapP≅`.  It exists because `Dec`'s client-facing `mapP` is genuinely
-- divariant: a caller may transport a decision along a retract.
record DivariantAnswer (𝒯 : AnswerFunctor) : Typeω where
  open AnswerFunctor 𝒯
  field
    Ans-dimap : {ℓA ℓB : Level} {A : TheorySet ℓA tt} {B : TheorySet ℓB tt}
      → ty A ⊢ ty B → ty B ⊢ ty A → ty (Ans A) ⊢ ty (Ans B)

-- `AnswerFunctor` constrains types, not behaviour: an instance is free to
-- define `Ans-≅ φ = <discard the answer>` and still typecheck.  These two
-- laws say `Ans` really is a functor on grammars-and-isomorphisms, and they
-- are what any theorem *about* the combinators has to start from.  Kept
-- separate so that sketching a new answer does not owe them up front.
record LawfulAnswer (𝒯 : AnswerFunctor) : Typeω where
  open AnswerFunctor 𝒯
  field
    Ans-≅-id : {ℓA : Level} {A : TheorySet ℓA tt}
      → Ans-≅ (id≅ {A = ty A}) ≡ id⊢
    Ans-≅-⋆ : {ℓA ℓB ℓC : Level}
      {A : TheorySet ℓA tt} {B : TheorySet ℓB tt} {C : TheorySet ℓC tt}
      (φ : ty A ≅ ty B) (ψ : ty B ≅ ty C)
      → Ans-≅ (φ ⋆≅ ψ) ≡ Ans-≅ ψ ∘⊢ Ans-≅ φ


module Combinators (𝒯 : AnswerFunctor) where
  open AnswerFunctor 𝒯 public

  ▷Ans-≅ : {t : ParserTag} {K : TheorySet ℓK tt} {L : TheorySet ℓL tt}
    → ty K ≅ ty L → ty (▷? t (Ans K)) ⊢ ty (▷? t (Ans L))
  ▷Ans-≅ φ = ▷map (Ans-≅ φ)

  ▷Ans-⊕& : {t : ParserTag} {K : TheorySet ℓK tt} {L : TheorySet ℓL tt}
    → ty (▷? t (Ans K)) & ty (▷? t (Ans L))
    ⊢ ty (▷? t (Ans (K ⊕Set L)))
  ▷Ans-⊕& = ▷map Ans-⊕& ∘⊢ ▷lax

  -- A parser for A turns answers about a grammar K into answers about A ⊗ K
  Parser : (ℓK : Level) → ParserTag → ParserTag → TheorySet ℓA tt → TheoryTy _ tt
  Parser ℓK a c A =
    &[ K ∈ TheorySet ℓK tt ]
      (ty (▷? a (Ans K)) ⇒ ty (▷? c (Ans (A ⊗Set K))))

  ParserSet : (ℓK : Level) (a c : ParserTag) → TheorySet ℓA tt → TheorySet _ tt
  ParserSet ℓK a c A =
    Parser ℓK a c A , isSet&ᴰ λ K → isSet⇒ (▷? c (Ans (A ⊗Set K)) .snd)

  mkP : {ℓK : Level} {a c : ParserTag} {A : TheorySet ℓA tt} {D : TheoryTy ℓD tt}
    → (∀ (K : TheorySet ℓK tt)
        → D & ty (▷? a (Ans K)) ⊢ ty (▷? c (Ans (A ⊗Set K))))
    → D ⊢ Parser ℓK a c A
  mkP f = &ᴰ-intro λ K → ⇒-intro (f K)

  pAt : {ℓK : Level} {a c : ParserTag} {A : TheorySet ℓA tt} {D : TheoryTy ℓD tt}
    → D ⊢ Parser ℓK a c A → (K : TheorySet ℓK tt)
    → D & ty (▷? a (Ans K)) ⊢ ty (▷? c (Ans (A ⊗Set K)))
  pAt p K = ⇒-app ∘⊢ ((π K ∘⊢ p) ,&p id⊢)

  pmore : {ℓK : Level} {c : ParserTag} {A : TheorySet ℓA tt}
    → Parser ℓK ⟨▷⟩ c A ⊢ Parser ℓK ⟨□⟩ c A
  pmore = mkP λ K → pAt id⊢ K ∘⊢ (id& ▷wk)

  pless : {ℓK : Level} {a : ParserTag} {A : TheorySet ℓA tt}
    → Parser ℓK a ⟨□⟩ A ⊢ Parser ℓK a ⟨▷⟩ A
  pless = mkP λ K → ▷wk ∘⊢ pAt id⊢ K

  -- weakening the domain tag, uniformly in the tag it starts at
  pw : {ℓK : Level} {a c : ParserTag} {A : TheorySet ℓA tt}
    → Parser ℓK a c A ⊢ Parser ℓK ⟨□⟩ c A
  pw {a = ⟨▷⟩} = pmore
  pw {a = ⟨□⟩} = id⊢

  -- Relabelling a parser along an isomorphism of grammars.  This is what a
  -- grammar's `roll`/`unroll` gives, now that those are known to be inverse.
  mapP≅ : {ℓK : Level} {a c : ParserTag}
    {A : TheorySet ℓA tt} {B : TheorySet ℓB tt}
    → ty A ≅ ty B → Parser ℓK a c A ⊢ Parser ℓK a c B
  mapP≅ φ = mkP λ K → ▷Ans-≅ (⊗≅ φ id≅) ∘⊢ pAt id⊢ K

  pApp : {ℓK : Level} {A : TheorySet ℓA tt} (K : TheorySet ℓK tt)
    → ty (▷ (ParserSet ℓK ⟨□⟩ ⟨□⟩ A)) & ty (▷ (Ans K))
    ⊢ ty (▷ (Ans (A ⊗Set K)))
  pApp K = ▷map (□here ∘⊢ pAt id⊢ K) ∘⊢ ▷lax ∘⊢ (id⊢ ,&p ▷δ□)

  -- Combinators under an arbitray hypothesis D
  module _ {D : TheoryTy ℓD tt} where

    infixr 15 _<|>_

    seq : {ℓK ℓB : Level} {a b c : ParserTag} {A : TheorySet ℓA tt}
      (B : TheorySet ℓB tt)
      → D ⊢ Parser (ℓ⊗ ℓB ℓK) b c A → D ⊢ Parser ℓK a b B
      → D ⊢ Parser ℓK a c (A ⊗Set B)
    seq B p q = mkP λ K →
      ▷Ans-≅ ⊗-assoc≅ ∘⊢ pAt p (B ⊗Set K) ∘⊢ (π₁ ,& pAt q K)

    _<|>_ : {ℓK : Level} {a c : ParserTag}
      {A : TheorySet ℓA tt} {B : TheorySet ℓB tt}
      → D ⊢ Parser ℓK a c A → D ⊢ Parser ℓK a c B
      → D ⊢ Parser ℓK a c (A ⊕Set B)
    (p <|> q) = mkP λ K →
      ▷Ans-≅ ⊗⊕-distL≅ ∘⊢ ▷Ans-⊕& ∘⊢ (pAt p K ,& pAt q K)

    tok : {ℓK : Level} (c : Alphabet) → D ⊢ Parser ℓK ⟨▷⟩ ⟨□⟩ (litSet c)
    tok c = mkP λ K → ▷□ (Ans-lit c) ∘⊢ π₂

    anyTok : {ℓK : Level} → D ⊢ Parser ℓK ⟨▷⟩ ⟨□⟩ charSet
    anyTok = mkP λ K → ▷□ Ans-any ∘⊢ π₂

    nil : {ℓK : Level} → D ⊢ Parser ℓK ⟨□⟩ ⟨□⟩ εSet
    nil = mkP λ K → ▷Ans-≅ ⊗ε-unit-l≅ ∘⊢ π₂

    -- a closed parser is available at every suffix
    box : {ℓK : Level} {A : TheorySet ℓA tt} → ⊤Ty ⊢ Parser ℓK ⟨□⟩ ⟨□⟩ A
      → D ⊢ Parser ℓK ⟨▷⟩ ⟨▷⟩ A
    box p = mkP λ K → pApp K ∘⊢ (▷next {t = ⟨▷⟩} p ,&p id⊢)

  □Ans-ε : {ℓK : Level} {D : TheoryTy ℓD tt} → D ⊢ ty (□ (Ans (ε↑Set ℓK)))
  □Ans-ε = ▷next {t = ⟨□⟩} (Ans-≅ lift≅ ∘⊢ Ans-ε)

  -- A parser under the hypothesis ⊤ is sufficent for answering about A
  runP : (ℓK : Level) {A : TheorySet ℓA tt}
    → ⊤Ty ⊢ Parser (ℓ-max ℓM ℓK) ⟨□⟩ ⟨□⟩ A → ⊤Ty ⊢ ty (Ans A)
  runP _ p =
    Ans-≅ ⊗ε↑-unit-r≅ ∘⊢ □here ∘⊢ pAt p (ε↑Set _) ∘⊢ (id⊢ ,& □Ans-ε)

  -- Build parsers as fixpoints
  module Fix {ℓA} (ℓK : Level) (A : TheorySet ℓA tt) where

    ℓ𝒦 : Level
    ℓ𝒦 = ℓ-max ℓM ℓK

    -- Call the hypothetical parser on a strictly smaller suffix
    call : ty (▷ (ParserSet ℓ𝒦 ⟨□⟩ ⟨□⟩ A)) ⊢ Parser ℓ𝒦 ⟨▷⟩ ⟨▷⟩ A
    call = mkP pApp

    -- Guarded fixpoints build closed parsers
    fix : ty (▷ (ParserSet ℓ𝒦 ⟨□⟩ ⟨□⟩ A)) ⊢ Parser ℓ𝒦 ⟨□⟩ ⟨□⟩ A
      → ⊤Ty ⊢ Parser ℓ𝒦 ⟨□⟩ ⟨□⟩ A
    fix = löbG {A = ParserSet ℓ𝒦 ⟨□⟩ ⟨□⟩ A}

    -- ...which are then used to answer
    runFix : ty (▷ (ParserSet ℓ𝒦 ⟨□⟩ ⟨□⟩ A)) ⊢ Parser ℓ𝒦 ⟨□⟩ ⟨□⟩ A
      → ⊤Ty ⊢ ty (Ans A)
    runFix φ = runP ℓK (fix φ)

-- The two combinators a covariant answer buys: `mapP` needs only the
-- forward map, and a parser may give up at any grammar.
module CovCombinators (𝒯 : AnswerFunctor) (cov : CovariantAnswer 𝒯) where
  open Combinators 𝒯
  open CovariantAnswer cov public

  mapP : {ℓK : Level} {a c : ParserTag}
    {A : TheorySet ℓA tt} {B : TheorySet ℓB tt}
    → ty A ⊢ ty B → Parser ℓK a c A ⊢ Parser ℓK a c B
  mapP f = mkP λ K → ▷map (Ans-map (f ,⊗ id⊢)) ∘⊢ pAt id⊢ K

  fail : {ℓK : Level} {a c : ParserTag} {A : TheorySet ℓA tt}
    {D : TheoryTy ℓD tt} → D ⊢ Parser ℓK a c A
  fail {c = c} = mkP λ K → ▷next {t = c} Ans-empty

-- ...and the one a divariant answer buys: relabelling a parser along a
-- `roll`/`unroll` pair.  This is what makes a *grammar* answer-generic.
module DivCombinators (𝒯 : AnswerFunctor) (div : DivariantAnswer 𝒯) where
  open Combinators 𝒯
  open DivariantAnswer div public

  ▷Ans-dimap : {t : ParserTag} {K : TheorySet ℓK tt} {L : TheorySet ℓL tt}
    → ty K ⊢ ty L → ty L ⊢ ty K
    → ty (▷? t (Ans K)) ⊢ ty (▷? t (Ans L))
  ▷Ans-dimap f g = ▷map (Ans-dimap f g)

  mapP± : {ℓK : Level} {a c : ParserTag}
    {A : TheorySet ℓA tt} {B : TheorySet ℓB tt}
    → ty A ⊢ ty B → ty B ⊢ ty A
    → Parser ℓK a c A ⊢ Parser ℓK a c B
  mapP± f g = mkP λ K → ▷Ans-dimap (f ,⊗ id⊢) (g ,⊗ id⊢) ∘⊢ pAt id⊢ K

-- What the laws buy: `Ans-≅ φ` is itself an isomorphism.  So an answer is
-- genuinely *transported* by a combinator, never merely mapped -- which is
-- the sentence this module's header asserts, now derived.
module LawfulCombinators (𝒯 : AnswerFunctor) (law : LawfulAnswer 𝒯) where
  open Combinators 𝒯
  open LawfulAnswer law public

  module _ {A B : TheorySet ℓA tt} (φ : ty A ≅ ty B) where

    Ans-≅-sec : Ans-≅ φ ∘⊢ Ans-≅ (inv≅ φ) ≡ id⊢
    Ans-≅-sec =
      sym (Ans-≅-⋆ (inv≅ φ) φ)
      ∙ cong (λ χ → Ans-≅ χ) (≅≡ (φ .sec) (φ .sec))
      ∙ Ans-≅-id

    Ans-≅-ret : Ans-≅ (inv≅ φ) ∘⊢ Ans-≅ φ ≡ id⊢
    Ans-≅-ret =
      sym (Ans-≅-⋆ φ (inv≅ φ))
      ∙ cong (λ χ → Ans-≅ χ) (≅≡ (φ .ret) (φ .ret))
      ∙ Ans-≅-id

    Ans≅ : ty (Ans A) ≅ ty (Ans B)
    Ans≅ .fun = Ans-≅ φ
    Ans≅ .inv = Ans-≅ (inv≅ φ)
    Ans≅ .sec = Ans-≅-sec
    Ans≅ .ret = Ans-≅-ret
