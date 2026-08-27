{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Predictive choice indexed by the alternatives, not by the cover's cells.

   `Decidable/Lookahead`'s `Predictive.choose` demands one branch per cell,
   so cells with no production need a `⊥Set↑` pad, and a nullable branch
   cannot pay `lead` at all -- which is why `Decidable/Productions` bolts a
   `nul : X → Bool` field and a trailing `<|>` on top.  Here the branches are
   indexed by whatever indexes them (production tags), the cover is reached
   only through `routeIn`, and cells with no branch are `nothing`.

   The nullable case is not repaired by this and cannot be: `E' ::= ε | '+' E`
   followed by another `E'` is genuinely ambiguous, so no route exists at that
   continuation.  Prediction of a nullable branch needs the goal to be indexed
   by its continuation -- the continuation-passed grammar -- not an end over
   continuations.  Until then such a branch is *tried*, by `_<|>_`, which is
   always sound. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Decidable.Routed
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; Unit* ; tt ; tt*)
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)

open import Theory.Instances.Monoid.Combinator.Decidable.Base Alphabet _≟_ ℓ public
  hiding (Maybe ; just ; nothing)
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⊗ε-unit-l⁻ ; ⊗ε-unit-r ; ⊗ε-unit-r⁻ ; ⊗⊕ᴰ-distL ; &⊕ᴰ-distR)
open import Theory.Type.Decidable.Route
  MonEqns Alphabet (λ _ → tt) listPresentation public

private variable ℓA ℓB ℓD : Level

-- Building routes from the one-token cover: coarsen `Λ₁` along a routing
-- of its cells.  This is the only table-shaped object in the development,
-- and it is a plain function `M₁ → Maybe Y`.

decM₁ : DiscreteEq M₁
decM₁ ε₁ ε₁ = Sum.inl Eq.refl
decM₁ ε₁ (tk c) = Sum.inr λ ()
decM₁ (tk c) ε₁ = Sum.inr λ ()
decM₁ (tk c) (tk d) = go (c ≟ d)
  where
  go : (c Eq.≡ d) Sum.⊎ ((c Eq.≡ d) → Empty.⊥)
     → (tk c Eq.≡ tk d) Sum.⊎ ((tk c Eq.≡ tk d) → Empty.⊥)
  go (Sum.inl Eq.refl) = Sum.inl Eq.refl
  go (Sum.inr ne) = Sum.inr λ where Eq.refl → ne Eq.refl

-- Coarsening ANY cover along a routing of its cells.  Nothing below is
-- specific to one-token lookahead: swap the cover and the same `Route`,
-- the same `choose` and the same fixpoint give LL(k) or LL-regular.
module PushOf {I : Type ℓAlph} (Λ : I → TheoryTy ℓM tt)
  (cov : Cover I Λ) (decI : DiscreteEq I)
  {Y : Type ℓAlph} (r : I → Maybe Y) where

  Fib : Maybe Y → Type ℓAlph
  Fib v = Σ[ b ∈ I ] (r b Eq.≡ v)

  PB : Maybe Y → TheoryTy ℓG tt
  PB v = LiftTheoryTy ℓG (⊕[ f ∈ Fib v ] Λ (f .fst))

  atCell : (b : I) → Λ b ⊢ PB (r b)
  atCell b = liftTy ∘⊢ σ⊕ (b , Eq.refl)

  covers : Cover (Maybe Y) PB
  covers .total =
    ⊕ᴰ-elim (λ b → σ⊕ (r b) ∘⊢ atCell b) ∘⊢ cov .total
  covers .disjoint v v' ne m
    (lift ((b , p) , t) , lift ((b' , p') , t')) = go (decI b b')
    where
    go : (b Eq.≡ b') Sum.⊎ ((b Eq.≡ b') → Empty.⊥) → ⊥Ty m
    go (Sum.inl Eq.refl) = Empty.rec (ne (same p p'))
      where
      same : {u u' : Maybe Y} → r b Eq.≡ u → r b Eq.≡ u' → u Eq.≡ u'
      same Eq.refl Eq.refl = Eq.refl
    go (Sum.inr nb) = cov .disjoint b b' nb m (t , t')

-- ...and the one-token cover is the instance we had.
module Push {Y : Type ℓAlph} (r : M₁ → Maybe Y) =
  PushOf Λ₁ lookaheadCover decM₁ r

-- Routed choice, over `Decidable/Base`'s parser.

module Choice
  {Y : Type ℓAlph} (decY : DiscreteEq Y)
  (C : Y → TheorySet ℓG tt)
  where

  isSetY : isSet Y
  isSetY = Discrete→isSet λ y y' → Sum.rec
    (λ p → yes (Eq.eqToPath p)) (λ ¬p → no λ p → ¬p (Eq.pathToEq p)) (decY y y')
    where open import Cubical.Relation.Nullary.Base using (yes ; no)

  RAlt : TheorySet _ tt
  RAlt = ⊕ᴰSet isSetY C

  -- one route per continuation: the branch a cell names, and a `⊥`-map for
  -- every branch it does not
  Guide : Type _
  Guide = (K : TheorySet ℓG tt) → Route (λ y → ty (C y) ⊗ ty K) ℓG

  private
    distL⁻ : (K : TheorySet ℓG tt)
      → (⊕[ y ∈ Y ] (ty (C y) ⊗ ty K)) ⊢ ty RAlt ⊗ ty K
    distL⁻ K = ⊕ᴰ-elim λ y → σ⊕ y ,⊗ id⊢

    commit : (g : Guide) (K : TheorySet ℓG tt)
      → ty (&ᴰSet (λ y → DecSet (C y ⊗Set K))) ⊢ DecTy (ty RAlt ⊗ ty K)
    commit g K =
      dec-map (distL⁻ K) (¬Ty-map ⊗⊕ᴰ-distL)
      ∘⊢ routeIn (λ y → ty (C y) ⊗ ty K) (g K) decY

  choose : {a c : ParserTag} {D : TheoryTy ℓD tt}
    → Guide → ((y : Y) → D ⊢ Parser ℓG a c (C y)) → D ⊢ Parser ℓG a c RAlt
  choose g p = mkP λ K →
    ▷map (commit g K) ∘⊢ ▷laxᴰ (λ y → DecSet (C y ⊗Set K))
    ∘⊢ (&ᴰ-intro λ y → pAt (p y) K)

-- The fixpoint over a family of nonterminals: the hypothesis is a
-- conjunction of guarded parsers, and `callAt` reads any of them at a
-- strict suffix.  `Decidable/Dyck`'s `Fix`, with the single grammar
-- replaced by a family.

module FixAll {X : Type ℓAlph} (A : X → TheorySet ℓG tt) where

  Pall : TheorySet _ tt
  Pall = &ᴰSet (λ x → ParserSet ℓG ⟨□⟩ ⟨□⟩ (A x))

  callAt : (x : X) → ty (▷ Pall) ⊢ Parser ℓG ⟨▷⟩ ⟨▷⟩ (A x)
  callAt x = mkP pApp ∘⊢ ▷map {t = ⟨▷⟩} (π x)

  parsers : ty (▷ Pall) ⊢ ty Pall → ⊤Ty ⊢ ty Pall
  parsers = löbG {A = Pall}

  decideAt : (ty (▷ Pall) ⊢ ty Pall) → (x : X) → Decidable (ty (A x))
  decideAt step x = runP ℓG (π x ∘⊢ parsers step)
