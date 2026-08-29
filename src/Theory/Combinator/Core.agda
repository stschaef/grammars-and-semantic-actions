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
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.FinData.Properties using (isSetFin)
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
open import Theory.Type.Product.Base σeq V vs 𝒫
open import Theory.Type.Product.Binary.Base σeq V vs 𝒫
open import Theory.Type.Cover.Base σeq V vs 𝒫
open import Theory.Type.Decidable.Base σeq V vs 𝒫
open import Theory.Type.Decidable.Route σeq V vs 𝒫

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

-- The one thing `⊗ᴰ` is not: a `Functor` code.  `Theory/Type/Code/Base`
-- has `⊗e`, whose slots are independent, so a grammar that needs the
-- dependency cannot be a `μ` and gets its `roll`/`unroll` written by hand
-- (twelve lines, and they are honest `⊢`-terms) instead of for free.
--
-- Closing that gap means adding a `⊗ᴰe` constructor, which every match on
-- `Functor` would then have to cover -- around seventeen sites across
-- `Code/Base`, `Inductive/HLevels`, `Code/Container` and
-- `Guarded/Justification`, all shared with the monoid development.  Worth
-- doing deliberately, not in passing.
--
-- Worth knowing before doing it: the dependency is an artefact of *named*
-- syntax.  `lam n t` scopes its body in `Γ , n`, and `n` is a slot value;
-- a de Bruijn `lam t` scopes it in `B ∷ Γ`, which mentions no slot at all.
-- So surface-syntax judgments need `⊗ᴰ` and core-syntax ones do not --
-- which is one more reason compilers go nameless early.

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


-- Reindexing a grammar along a map of model elements -- possibly across
-- sorts, since nothing here relates the two.
reTy : {s s' : S} → (↓M s → ↓M s') → TheoryTy ℓA s' → TheoryTy ℓA s
reTy f A m = A (f m)

reSet : {s s' : S} → (↓M s → ↓M s') → TheorySet ℓA s' → TheorySet ℓA s
reSet f (A , sA) = reTy f A , λ m → sA (f m)


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

    -- ...and the conjunctive counterpart.  A rule with a side condition
    -- *and* a premise in the same slot needs this: an operation has exactly
    -- its arity many slots, so a condition that is not itself an argument
    -- has to ride along with one.  Linear typing's application rule is the
    -- case in point -- the partition check travels with the function.
    Ans-&& : {ℓA ℓB : Level} {s : S} {A : TheorySet ℓA s} {B : TheorySet ℓB s}
      → ty (Ans A) & ty (Ans B) ⊢ ty (Ans (A &Set B))

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
    --
    -- Known gap: a *nullary* operation has no slot, so this rule cannot
    -- refute one, and a side condition attached to one has nowhere to ride.
    -- Two clients hit it independently -- `Match` at `vtrueOp`, `Layout` at
    -- `nilOp` -- and neither needed a change here: `Ans-map&` will do it,
    -- since the cover cell is exactly the knowledge that makes the grammar
    -- empty, and `Ans-&&` will attach the condition at the node rather than
    -- at a slot.  `Layout`'s form is the better convention: state every
    -- operation's side condition as `⊗ᴰSet o (Slots o S) &Set SideSet o S`
    -- and `Slots` stays pure recursive calls, where `Linear` instead hangs
    -- its partition check off the function's slot.  Worth adopting before
    -- the next client repeats the choice a third way.
    Ans-node : {ℓA : Level} (o : σ .ops) → Precise o
      → {As : NodeArgs ℓA o} {ms : interpIn o ↓M}
      → ((a : arities σ o) → ty (Ans (As ms a)) (ms a))
      → ty (Ans (⊗ᴰSet o As)) (op o ms)

    -- An answer is *pointwise* in the model element: an answer at `f m`
    -- for `A` is an answer at `m` for `A` reindexed along `f`.
    --
    -- `Ans-node` is this same move for the one map a signature supplies --
    -- a slot's projection out of its node -- and that is all a judgment
    -- whose premises are *subterms* ever needs.  A judgment that is a
    -- *machine* needs more: its premise sits at a state computed from the
    -- conclusion's, and no operation of any signature produces that state
    -- from the premise's.  `Instances/Unify` is the case in point, where
    -- the state is the equation stack with a substitution applied.
    --
    -- This is much less than a bind: the reindexing is a map of *model
    -- elements*, fixed before any answer is asked, so a later premise
    -- still cannot depend on an earlier premise's derivation.  Every
    -- answer defined by cases on `A m` satisfies it, which is all three --
    -- `Dec` and `Maybe` by the identity, `ND` by the list isomorphism it
    -- is already defined through.
    Ans-re : {ℓA : Level} {s s' : S} {A : TheorySet ℓA s'}
      (f : ↓M s → ↓M s') → reTy f (ty (Ans A)) ⊢ ty (Ans (reSet f A))


-- A covariant answer additionally has a plain `fmap` and an *empty answer*
-- at any grammar.  `Dec` has neither, and the second is the interesting
-- refusal: `⊤Ty ⊢ DecTy A` at an arbitrary `A` is a decision procedure, not
-- a default.  One cannot decline to decide.
record CovariantAnswer (𝒯 : AnswerFunctor) : Typeω where
  open AnswerFunctor 𝒯
  field
    Ans-fmap : {ℓA ℓB : Level} {s : S}
      {A : TheorySet ℓA s} {B : TheorySet ℓB s}
      → ty A ⊢ ty B → ty (Ans A) ⊢ ty (Ans B)

    Ans-empty : {ℓA : Level} {s : S} {A : TheorySet ℓA s} → ⊤Ty ⊢ ty (Ans A)

-- Committing to one summand of an indexed sum.  `_<|>_` asks every
-- alternative and glues the answers; `Ans-route` is told by a `Route` which
-- alternative the model is in, and answers from that one branch.
--
-- This is the field the framework was missing, and it is what a judgment
-- whose *premise index is an output* needs.  When a rule reads
--
--     ⊕[ y ∈ Y ] Φ y      -- some `y` works, and the checker must find it
--
-- the checker cannot consult all of `Y`: `Y` need not be finite, and even
-- when it is, asking every alternative is not what a resolver does.  A
-- `Route` supplies a `Cover` of the model by `Maybe Y` -- `total` says the
-- model lands in a named cell or in the `nothing` cell, `disjoint` says it
-- lands in at most one -- so the answer is asked only where the cover
-- points.
--
-- It is the one field whose two implementations are genuinely different
-- arguments rather than the same argument transcribed.  At `Dec` the named
-- branch may come back `no`, and the sum must then be refuted *outright*:
-- that is `routeIn`, and it is the cover's `disjoint` that kills every
-- unnamed alternative.  A covariant answer has no refutation to propagate
-- and needs none -- `Ans-empty` answers the `nothing` cell, and a branch
-- that yields nothing makes the sum yield nothing -- so `FromCov.committing`
-- derives it once.  Neither half follows from `AnswerFunctor` alone: an
-- answer has to say what it does with the alternatives it did not take.
record CommittingAnswer (𝒯 : AnswerFunctor) : Typeω where
  open AnswerFunctor 𝒯
  field
    Ans-route : {ℓY ℓA ℓB : Level} {s : S} {Y : Type ℓY}
      (sY : isSet Y) (Φ : Y → TheorySet ℓA s)
      → Route (λ y → ty (Φ y)) ℓB → DiscreteEq Y
      → ty (&ᴰSet (λ y → Ans (Φ y))) ⊢ ty (Ans (⊕ᴰSet sY Φ))

-- What a covariant answer is, as a committing one: observe the cover, and
-- dispose of every cell not taken by `Ans-empty`.  No refutation travels
-- anywhere, which is why `Maybe` and `ND` route without ever spending the
-- cover's `disjoint`, while `Dec`'s `routeIn` spends nothing else.
module FromCov (𝒯 : AnswerFunctor) (cov : CovariantAnswer 𝒯) where
  open AnswerFunctor 𝒯
  open CovariantAnswer cov

  committing : CommittingAnswer 𝒯
  committing .CommittingAnswer.Ans-route {Y = Y} sY Φ R decY =
    ⊕ᴰ-elim step ∘⊢ &⊕ᴰ-dist
    ∘⊢ (id⊢ ,& (R .Route.cov .total ∘⊢ ⊤Ty-intro))
    where
    Ds : TheoryTy _ _
    Ds = ty (&ᴰSet (λ y → Ans (Φ y)))

    step : (v : Maybe Y) → Ds & R .Route.B v ⊢ ty (Ans (⊕ᴰSet sY Φ))
    step nothing = Ans-empty ∘⊢ ⊤Ty-intro
    step (just y₀) = Ans-fmap (σ⊕ y₀) ∘⊢ π y₀ ∘⊢ π₁

-- ...and the combinator that is `Ans-route`'s opposite number: ask every
-- alternative of a *finite* sum and keep all the answers.  No cover, no
-- `disjoint`, no commitment -- and correspondingly no way for the caller to
-- learn which alternative was taken, since more than one may have been.
--
-- `Dec` cannot have it, and the reason is not an oversight: `Ans-empty` is
-- the base case, and a decision cannot answer `⊕[ i ∈ Fin 0 ] Φ i` without
-- refuting it, which is a decision procedure.  So the split is exactly:
-- an answer that can commit routes, and an answer that can give up
-- enumerates.  A judgment whose alternatives are *not* known exclusive is
-- available only to the second kind -- which is why an incoherent instance
-- table is visible at `ND` and unwritable at `Dec`.
module CovCombinators (𝒯 : AnswerFunctor) (cov : CovariantAnswer 𝒯) where
  open AnswerFunctor 𝒯
  open CovariantAnswer cov public

  Ans-anyFin : {ℓA : Level} {s : S} {n : ℕ} {D : TheoryTy ℓD s}
    (Φ : Fin n → TheorySet ℓA s)
    → ((i : Fin n) → D ⊢ ty (Ans (Φ i)))
    → D ⊢ ty (Ans (⊕ᴰSet isSetFin Φ))
  Ans-anyFin {n = zero} Φ ps = Ans-empty ∘⊢ ⊤Ty-intro
  Ans-anyFin {n = suc n} Φ ps =
    Ans-fmap glue ∘⊢ Ans-⊕& ∘⊢ (ps zero ,& Ans-anyFin (λ i → Φ (suc i)) tail)
    where
    tail : (i : Fin n) → _ ⊢ ty (Ans (Φ (suc i)))
    tail i = ps (suc i)

    glue : ty (Φ zero) ⊕ (⊕[ i ∈ Fin n ] ty (Φ (suc i)))
         ⊢ ⊕[ i ∈ Fin (suc n) ] ty (Φ i)
    glue = ⊕-elim (σ⊕ zero) (⊕ᴰ-elim λ i → σ⊕ (suc i))


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

