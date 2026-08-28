{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Combinators for an arbitrary finitary algebraic theory.

   `Theory/Instances/Monoid/Combinator/Core` is these combinators at the
   free monoid: there a grammar is a predicate on strings, `⊗` is
   concatenation, and a parser is continuation-passing because a match
   consumes a *prefix* and leaves a suffix for the continuation.

   Nothing outside the monoid has that shape.  For a general signature the
   operations are constructors, not an associative product: a node says
   "`m` is `op o ms` and each `ms a` satisfies its slot", and there is no
   leftover.  So the continuation-passing disappears and what is left is
   smaller than the monoid development, not larger:

     * a `Checker` is `∀ x → ⊤Ty ⊢ Ans (A x)` -- no `&[ K ]` end, no
       `ParserTag`, no `pmore`/`pless`/`pw` weakening;
     * the guard is `Theory/Type/Later/Indexed`'s `GuardedIndexed`, already
       generic in the sort *and* the index, so `löb` is reused verbatim;
     * `Ans-lit`, `Ans-any` and `Ans-ε` -- three token rules that only make
       sense for a generated free monoid -- collapse to `Ans-node`, which
       applies to every operation of every signature.

   What replaces "the alphabet is discrete" is `Precise`: an operation whose
   decomposition is unique.  A free term algebra has it for every operation
   (`Theory/Free/Term`); the free monoid has it only for `literal c ⊗ -`,
   which is why that development has token rules rather than a node rule.

   The node is `⊗ᴰ`, not `Operation/Base`'s `⊗ᵘ`: the slot grammars are
   indexed by the *whole* splitting, so a later slot may depend on an
   earlier slot's value.  `⊗ᵘ` -- independent slots -- cannot state a
   binder, since the scope of `lam n t` is `Γ , n` and `n` is slot zero.
   `⊗ᵘ` is the constant case.

   Case analysis is by `look`, over a `Cover` of the model -- the sibling of
   the monoid development's `look⊗` over the lookahead cover.  For a free
   term algebra the cover is by head operation: `total` is the algebra's
   induction principle and `disjoint` is no-confusion, so prediction is
   always LL(1) and there is nothing here that resembles a window or a
   lookahead width.

   `Ans-map&` carries a hypothesis because that is what makes relabelling a
   `⊢`-term.  A grammar and one of its unfoldings agree only where the
   term's head is known, and the cover's cell is exactly that knowledge; a
   naked `Ans-map` would have to be pointwise. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
import Theory.Type.Later.Indexed as LI
module Theory.Combinator.Core
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
import Cubical.Data.Equality as Eq

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.HLevels σeq V vs 𝒫
open import Theory.Type.Top.Base σeq V vs 𝒫
open import Theory.Type.Bottom.Base σeq V vs 𝒫
open import Theory.Type.Function.Base σeq V vs 𝒫
open import Theory.Type.Sum.Base σeq V vs 𝒫
open import Theory.Type.Sum.Binary.Base σeq V vs 𝒫
open import Theory.Type.Product.Binary.Base σeq V vs 𝒫
open import Theory.Type.Cover.Base σeq V vs 𝒫
open import Theory.Type.Decidable.Base σeq V vs 𝒫

private variable ℓA ℓB ℓC ℓD ℓH ℓX ℓY ℓΛ ℓ< : Level

isPropModelEq : {s : S} {x y : ↓M s} → isProp (x Eq.≡ y)
isPropModelEq {s} =
  isOfHLevelRetractFromIso 1 (invIso Eq.PathIsoEq) (M .fst s .snd _ _)

DecSet : {s : S} → TheorySet ℓA s → TheorySet ℓA s
DecSet (A , sA) = DecTy A , isSet⊕ sA (isSet⇒ isSet⊥Ty)

-- Case analysis over a cover: `Λ` classifies the model, and a term is
-- built by giving a term at each cell.  This is `look⊗` with the lookahead
-- cover replaced by whatever cover the instance has.
private
  &⊕ᴰ-dist : {s : S} {Y : Type ℓY} {Λ : Y → TheoryTy ℓΛ s}
    {D : TheoryTy ℓD s} → D & (⊕[ y ∈ Y ] Λ y) ⊢ ⊕[ y ∈ Y ] (D & Λ y)
  &⊕ᴰ-dist m (d , (y , a)) = y , (d , a)

look : {s : S} {Y : Type ℓY} {Λ : Y → TheoryTy ℓΛ s}
  {C : TheoryTy ℓC s} {D : TheoryTy ℓD s}
  → Cover Y Λ → ((y : Y) → D & Λ y ⊢ C) → D ⊢ C
look cov br = ⊕ᴰ-elim br ∘⊢ &⊕ᴰ-dist ∘⊢ (id⊢ ,& (cov .total ∘⊢ ⊤Ty-intro))


-- The decomposition of `m` along `o`, as a grammar, and the operations for
-- which it is unique.  `NodeAt o` is the cell of the node cover; `Precise o`
-- is what makes it a proposition, and what lets a refutation at one slot
-- refute the whole node.
NodeAt : (o : σ .ops) → TheoryTy ℓM (σ .resultSort o)
NodeAt o m = Σ[ ms ∈ interpIn o ↓M ] (op o ms Eq.≡ m)

Precise : (o : σ .ops) → Type ℓM
Precise o = (m : ↓M (σ .resultSort o)) → isProp (NodeAt o m)

isSetNodeAt : (o : σ .ops) → Precise o → isSetTheoryTy (NodeAt o)
isSetNodeAt o prec m = isProp→isSet (prec m)

NodeAtSet : (o : σ .ops) → Precise o → TheorySet ℓM (σ .resultSort o)
NodeAtSet o prec = NodeAt o , isSetNodeAt o prec

-- The slots of a node, each a grammar at its own sort, all of them free to
-- mention the splitting.  A binder is the case that needs the dependency.
NodeArgs : (ℓA : Level) (o : σ .ops) → Type _
NodeArgs ℓA o =
  (ms : interpIn o ↓M) (a : arities σ o) → TheorySet ℓA (σ .sortOf o a)

⊗ᴰ : (o : σ .ops) → NodeArgs ℓA o
   → TheoryTy (ℓ-max ℓM ℓA) (σ .resultSort o)
⊗ᴰ o As m =
  Σ[ ms ∈ interpIn o ↓M ]
    ((op o ms Eq.≡ m) × ((a : arities σ o) → ty (As ms a) (ms a)))

isSet⊗ᴰ : (o : σ .ops) (As : NodeArgs ℓA o) → isSetTheoryTy (⊗ᴰ o As)
isSet⊗ᴰ o As m =
  isSetΣ (isSetΠ λ a → M .fst (σ .sortOf o a) .snd) λ ms →
  isSet× (isProp→isSet isPropModelEq) (isSetΠ λ a → isSetTy (As ms a) (ms a))

⊗ᴰSet : (o : σ .ops) → NodeArgs ℓA o
      → TheorySet (ℓ-max ℓM ℓA) (σ .resultSort o)
⊗ᴰSet o As = ⊗ᴰ o As , isSet⊗ᴰ o As

-- Introduction and elimination, in the shape `Operation/Base` states them
-- for `⊗ᵘ`: at `op o ms`, a witness in each slot.
node-mk : {o : σ .ops} {As : NodeArgs ℓA o} {ms : interpIn o ↓M}
  → ((a : arities σ o) → ty (As ms a) (ms a))
  → ty (⊗ᴰSet o As) (op o ms)
node-mk {ms = ms} ws = ms , Eq.refl , ws

node-elim : {o : σ .ops} {As : NodeArgs ℓA o}
  {C : TheoryTy ℓB (σ .resultSort o)}
  → ({ms : interpIn o ↓M}
      → ((a : arities σ o) → ty (As ms a) (ms a)) → C (op o ms))
  → ⊗ᴰ o As ⊢ C
node-elim f _ (ms , Eq.refl , ws) = f ws

-- forgetting the slots: a node is in its own cell of the node cover
node-shape : {o : σ .ops} {As : NodeArgs ℓA o} → ⊗ᴰ o As ⊢ NodeAt o
node-shape m t = t .fst , t .snd .fst


record AnswerFunctor : Typeω where
  field
    ℓAns : Level → Level
    Ans : {ℓA : Level} {s : S} → TheorySet ℓA s → TheorySet (ℓAns ℓA) s

    -- Relabelling, under a hypothesis.  Divariant, as in the monoid
    -- development's `DivariantAnswer`: `Dec` moves a refutation backwards
    -- and the covariant answers drop the second map.  `H` is what a cover
    -- cell supplies -- "this term is a node of operation `o`" -- and it is
    -- what makes both maps `⊢`-terms.
    Ans-map& : {ℓA ℓB ℓH : Level} {s : S}
      {A : TheorySet ℓA s} {B : TheorySet ℓB s} {H : TheoryTy ℓH s}
      → ty A & H ⊢ ty B → ty B & H ⊢ ty A
      → ty (Ans A) & H ⊢ ty (Ans B)

    Ans-⊕& : {ℓA ℓB : Level} {s : S} {A : TheorySet ℓA s} {B : TheorySet ℓB s}
      → ty (Ans A) & ty (Ans B) ⊢ ty (Ans (A ⊕Set B))

    -- Every answer can read a decision.  This is how a side condition --
    -- "this name is in scope", "these two types agree" -- enters a grammar
    -- without the grammar naming an answer, and it is the `⊢`-level form of
    -- what `Dec`, `Maybe` and `ND` each do with a `yes`/`no`.
    Ans-ofDec : {ℓA : Level} {s : S} {A : TheorySet ℓA s}
      → ty (DecSet A) ⊢ ty (Ans A)

    -- The node rule, replacing the monoid's three token rules, in the shape
    -- `Operation/Base` states `⊗ᵘ-intro`: at `op o ms`, an answer at each
    -- slot.  `Precise o` is what lets a refutation at one slot refute the
    -- node.
    Ans-node : {ℓA : Level} (o : σ .ops) → Precise o
      → {As : NodeArgs ℓA o} {ms : interpIn o ↓M}
      → ((a : arities σ o) → ty (Ans (As ms a)) (ms a))
      → ty (Ans (⊗ᴰSet o As)) (op o ms)


-- The combinators.  `X` indexes the mutually recursive family -- one
-- component per nonterminal, per context, per (context, type) -- and `O` is
-- the well-founded order the recursion descends on.  For the monoid that
-- order is the proper suffix; for a term algebra the proper subterm, and
-- `GuardedIndexed` does not care which.
module Combinators (𝒯 : AnswerFunctor)
  {X : Type ℓX} (xs : X → S) (O : LI.IPtOrder σeq V vs 𝒫 xs ℓ<) where

  open AnswerFunctor 𝒯 public
  open LI.GuardedIndexed σeq V vs 𝒫 xs O public

  Fam : (ℓA : Level) → Type _
  Fam ℓA = (x : X) → TheorySet ℓA (xs x)

  -- the family of answers, as something `▷` can delay
  AnsFam : Fam ℓA → SetFam (ℓAns ℓA)
  AnsFam A = (λ x → ty (Ans (A x))) , λ x m → isSetTy (Ans (A x)) m

  -- What a grammar owes: an answer at every index, given delayed answers at
  -- every strictly smaller position.
  Step : Fam ℓA → Type _
  Step A = ∀ x → ▷ (AnsFam A) x ⊢ ty (Ans (A x))

  Checker : Fam ℓA → Type _
  Checker A = ∀ x → ⊤Ty ⊢ ty (Ans (A x))

  fix : {A : Fam ℓA} → Step A → Checker A
  fix {A = A} φ = Fam▷.löb (AnsFam A .fst) (AnsFam A .snd) φ

  -- Consulting the hypothesis at a strictly smaller position.  This is the
  -- whole of `call`/`callAt`/`pApp` from the monoid development: with no
  -- continuation to thread, it is `▷app`.
  callAt : {A : Fam ℓA} (x' : X) {x : X} {m : ↓M (xs x)} {m' : ↓M (xs x')}
    → (x' , m') < (x , m) → ▷ (AnsFam A) x m → ty (Ans (A x')) m'
  callAt {A = A} x' lt β = ▷app (AnsFam A) lt β

  -- relabelling with nothing assumed
  Ans-map : {s : S} {A : TheorySet ℓA s} {B : TheorySet ℓB s}
    → ty A ⊢ ty B → ty B ⊢ ty A → ty (Ans A) ⊢ ty (Ans B)
  Ans-map f g = Ans-map& (f ∘⊢ π₁) (g ∘⊢ π₁) ∘⊢ (id⊢ ,& ⊤Ty-intro)

  module _ {s : S} {D : TheoryTy ℓD s} where

    infixr 15 _<|>_

    _<|>_ : {A : TheorySet ℓA s} {B : TheorySet ℓB s}
      → D ⊢ ty (Ans A) → D ⊢ ty (Ans B) → D ⊢ ty (Ans (A ⊕Set B))
    (p <|> q) = Ans-⊕& ∘⊢ (p ,& q)

    -- a side condition, decided by the grammar and read by the answer
    side : {A : TheorySet ℓA s} → Decidable (ty A) → D ⊢ ty (Ans A)
    side d = Ans-ofDec ∘⊢ d ∘⊢ ⊤Ty-intro

    -- a grammar with no parse anywhere
    none : {A : TheorySet ℓA s} → (⊤Ty ⊢ ¬Ty (ty A)) → D ⊢ ty (Ans A)
    none n = side (dec-no ∘⊢ n)
