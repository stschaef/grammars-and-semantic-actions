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
     * the guard is `Theory/Type/Later/Indexed`'s `GuardedIndexed`, which
       is already generic in the sort *and* the index, so `löb` is reused
       verbatim rather than re-justified;
     * `Ans-lit`, `Ans-any` and `Ans-ε` -- three token rules that only make
       sense for a generated free monoid -- collapse to one field,
       `Ans-node`, which applies to every operation of every signature.

   What replaces "the alphabet is discrete" is `Precise`: an operation whose
   decomposition is unique.  For a free term algebra that is constructor
   injectivity and holds of every operation; for the free monoid it holds
   only of `literal c ⊗ -`, which is exactly why the monoid version has a
   token rule rather than a node rule.

   The node is `⊗ᴰ`, not `Operation/Base`'s `⊗ᵘ`: the slot grammars are
   indexed by the *whole* splitting, so a later slot may depend on an
   earlier slot's value.  `⊗ᵘ` -- independent slots -- cannot state a
   binder, since the scope of `lam n t` is `Γ , n` and `n` is slot zero.
   Nothing else changes: `⊗ᵘ` is the constant case.

   The five fields are pointwise where the monoid version is `⊢`-level.
   That is deliberate: an answer must dispose of a *particular* term, and
   asking for the disposal one term at a time is what makes `Ans-node`
   instantiable at `Dec`, `Maybe` and `ND` in a handful of lines each. -}
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
open import Theory.Type.Sum.Binary.Base σeq V vs 𝒫
open import Theory.Type.Product.Binary.Base σeq V vs 𝒫

private variable ℓA ℓB ℓD ℓX ℓ< : Level

isPropModelEq : {s : S} {x y : ↓M s} → isProp (x Eq.≡ y)
isPropModelEq {s} =
  isOfHLevelRetractFromIso 1 (invIso Eq.PathIsoEq) (M .fst s .snd _ _)

-- The decomposition of `m` along `o`, and the operations for which it is
-- unique.  `Ans-node` needs this to *refute*: a refutation of one slot is a
-- refutation of the node only when there is no other way to decompose.
Split : (o : σ .ops) → ↓M (σ .resultSort o) → Type ℓM
Split o m = Σ[ ms ∈ interpIn o ↓M ] (op o ms Eq.≡ m)

Precise : (o : σ .ops) → Type ℓM
Precise o = (m : ↓M (σ .resultSort o)) → isProp (Split o m)

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

-- The node introduction, as data: a splitting and a witness at each slot.
node-mk : {o : σ .ops} {As : NodeArgs ℓA o} {ms : interpIn o ↓M}
  → ((a : arities σ o) → ty (As ms a) (ms a))
  → ty (⊗ᴰSet o As) (op o ms)
node-mk {ms = ms} ws = ms , Eq.refl , ws

-- ...and its elimination, which projects the splitting rather than matching
-- it, so nothing forces the equation.
node-elim : {o : σ .ops} {As : NodeArgs ℓA o}
  {C : TheoryTy ℓB (σ .resultSort o)}
  → ((m : ↓M (σ .resultSort o)) (ms : interpIn o ↓M) → op o ms Eq.≡ m
      → ((a : arities σ o) → ty (As ms a) (ms a)) → C m)
  → ⊗ᴰ o As ⊢ C
node-elim f m t = f m (t .fst) (t .snd .fst) (t .snd .snd)


record AnswerFunctor : Typeω where
  field
    ℓAns : Level → Level
    Ans : {ℓA : Level} {s : S} → TheorySet ℓA s → TheorySet (ℓAns ℓA) s

    -- Divariant, as in the monoid development's `DivariantAnswer`: `Dec`
    -- moves a refutation backwards, the covariant answers drop the second
    -- map.  There is no separate action on isomorphisms because nothing
    -- here transports along a monoidal structure -- there is none.
    --
    -- Pointwise, not `⊢`-level, and that matters.  When an operation is
    -- indexed by external data -- `appOp B`, an application annotated with
    -- its argument type -- there are infinitely many operations, so a
    -- grammar cannot unroll to a *sum* over head constructors the way
    -- `Scope` does.  It unrolls to one node per term, and relabelling that
    -- node needs a map only at the term in hand.  `Ans-map` below is the
    -- uniform case.
    Ans-mapAt : {ℓA ℓB : Level} {s : S} {A : TheorySet ℓA s} {B : TheorySet ℓB s}
      {m : ↓M s}
      → (ty A m → ty B m) → (ty B m → ty A m)
      → ty (Ans A) m → ty (Ans B) m

    Ans-⊕& : {ℓA ℓB : Level} {s : S} {A : TheorySet ℓA s} {B : TheorySet ℓB s}
      → ty (Ans A) & ty (Ans B) ⊢ ty (Ans (A ⊕Set B))

    -- Every answer can consume a decision at a point.  This is how a side
    -- condition -- "this name is in scope", "these two types are equal" --
    -- enters a grammar without the grammar naming an answer: the author
    -- supplies a decision, and each backend reads it its own way (`Dec`
    -- keeps it, `Maybe` forgets the refutation, `ND` enumerates zero or one).
    -- `Ans-void` below is the `no` half, which is all the combinators need.
    Ans-dec : {ℓA : Level} {s : S} {A : TheorySet ℓA s} {m : ↓M s}
      → ty A m Sum.⊎ (ty A m → Empty.⊥) → ty (Ans A) m

    -- The node rule, replacing the monoid's three token rules.  Answers at
    -- the slots give an answer at the node; `Precise o` is what lets a
    -- refutation at one slot refute the node.
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

  module _ {s : S} {D : TheoryTy ℓD s} where

    infixr 15 _<|>_

    _<|>_ : {A : TheorySet ℓA s} {B : TheorySet ℓB s}
      → D ⊢ ty (Ans A) → D ⊢ ty (Ans B) → D ⊢ ty (Ans (A ⊕Set B))
    (p <|> q) = Ans-⊕& ∘⊢ (p ,& q)

    -- a grammar with no parse anywhere
    none : {A : TheorySet ℓA s}
      → (∀ m → ty A m → Empty.⊥) → D ⊢ ty (Ans A)
    none f m _ = Ans-dec (Sum.inr (f m))

    -- a side condition, decided by the grammar and read by the answer
    side : {A : TheorySet ℓA s}
      → (∀ m → ty A m Sum.⊎ (ty A m → Empty.⊥)) → D ⊢ ty (Ans A)
    side d m _ = Ans-dec (d m)

  -- the uniform relabelling, from the pointwise one
  Ans-map : {s : S} {A : TheorySet ℓA s} {B : TheorySet ℓB s}
    → ty A ⊢ ty B → ty B ⊢ ty A → ty (Ans A) ⊢ ty (Ans B)
  Ans-map f g m = Ans-mapAt (f m) (g m)

  mapA : {s : S} {A : TheorySet ℓA s} {B : TheorySet ℓB s} {D : TheoryTy ℓD s}
    → ty A ⊢ ty B → ty B ⊢ ty A → D ⊢ ty (Ans A) → D ⊢ ty (Ans B)
  mapA f g p = Ans-map f g ∘⊢ p
