{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
-- Standing hypothesis: `Precise o` (unique decomposition); free term
-- algebras have it for every operation.
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

open import Theory.Type.Distributivity σeq V vs 𝒫 using (&⊕ᴰ-distR)

look : {s : S} {Y : Type ℓY} {Λ : Y → TheoryTy ℓΛ s}
  {C : TheoryTy ℓC s} {D : TheoryTy ℓD s}
  → Cover Y Λ → ((y : Y) → D & Λ y ⊢ C) → D ⊢ C
look cov br = ⊕ᴰ-elim br ∘⊢ &⊕ᴰ-distR ∘⊢ (id⊢ ,& (cov .total ∘⊢ ⊤Ty-intro))


-- `Precise o` lets a refutation at one slot refute the whole node.
NodeAt : (o : σ .ops) → TheoryTy ℓM (σ .resultSort o)
NodeAt o m = Σ[ ms ∈ interpIn o ↓M ] (op o ms Eq.≡ m)

Precise : (o : σ .ops) → Type ℓM
Precise o = (m : ↓M (σ .resultSort o)) → isProp (NodeAt o m)

isSetNodeAt : (o : σ .ops) → Precise o → isSetTheoryTy (NodeAt o)
isSetNodeAt o prec m = isProp→isSet (prec m)
-- Slots may depend on the splitting; binders need this.
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

-- Known gap: `⊗ᴰ` is not a `Functor` code (`⊗e` has independent slots), so
-- dependent grammars cannot be a `μ`; closing it means a `⊗ᴰe` constructor
-- and ~17 new match sites.  The dependency is an artefact of named syntax.

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
reTy : {s s' : S} → (↓M s → ↓M s') → TheoryTy ℓA s' → TheoryTy ℓA s
reTy f A m = A (f m)

reSet : {s s' : S} → (↓M s → ↓M s') → TheorySet ℓA s' → TheorySet ℓA s
reSet f (A , sA) = reTy f A , λ m → sA (f m)


record AnswerFunctor : Typeω where
  field
    ℓAns : Level → Level
    Ans : {ℓA : Level} {s : S} → TheorySet ℓA s → TheorySet (ℓAns ℓA) s

    -- divariant: `Dec` moves a refutation backwards
    Ans-map& : {ℓA ℓB ℓH : Level} {s : S}
      {A : TheorySet ℓA s} {B : TheorySet ℓB s} {H : TheoryTy ℓH s}
      → ty A & H ⊢ ty B → ty B & H ⊢ ty A
      → ty (Ans A) & H ⊢ ty (Ans B)

    Ans-⊕& : {ℓA ℓB : Level} {s : S} {A : TheorySet ℓA s} {B : TheorySet ℓB s}
      → ty (Ans A) & ty (Ans B) ⊢ ty (Ans (A ⊕Set B))

    -- Convention: side conditions conjoin with the node, not a slot
    -- (nullary operations have no slot).
    Ans-&& : {ℓA ℓB : Level} {s : S} {A : TheorySet ℓA s} {B : TheorySet ℓB s}
      → ty (Ans A) & ty (Ans B) ⊢ ty (Ans (A &Set B))

    Ans-ofDec : {ℓA : Level} {s : S} {A : TheorySet ℓA s}
      → ty (DecSet A) ⊢ ty (Ans A)

    -- Known gap: cannot refute a nullary operation (no slot); `Match` at
    -- `vtrueOp` and `Layout` at `nilOp` use `Ans-map&` instead.
    Ans-node : {ℓA : Level} (o : σ .ops) → Precise o
      → {As : NodeArgs ℓA o} {ms : interpIn o ↓M}
      → ((a : arities σ o) → ty (Ans (As ms a)) (ms a))
      → ty (Ans (⊗ᴰSet o As)) (op o ms)

    -- Pointwise reindexing only; too weak for judgments whose premise
    -- state is computed from the conclusion's (`Instances/Unify`).
    Ans-re : {ℓA : Level} {s s' : S} {A : TheorySet ℓA s'}
      (f : ↓M s → ↓M s') → reTy f (ty (Ans A)) ⊢ ty (Ans (reSet f A))


-- `Dec` has neither: `Ans-empty` at arbitrary `A` would be a decision
-- procedure.
record CovariantAnswer (𝒯 : AnswerFunctor) : Typeω where
  open AnswerFunctor 𝒯
  field
    Ans-fmap : {ℓA ℓB : Level} {s : S}
      {A : TheorySet ℓA s} {B : TheorySet ℓB s}
      → ty A ⊢ ty B → ty (Ans A) ⊢ ty (Ans B)

    Ans-empty : {ℓA : Level} {s : S} {A : TheorySet ℓA s} → ⊤Ty ⊢ ty (Ans A)

-- Commit to the one summand named by a `Route`; needed when `Y` need not be
-- finite.  At `Dec` a `no` refutes the whole sum (`routeIn`); `FromCov`
-- derives the covariant case from `Ans-empty`.
record CommittingAnswer (𝒯 : AnswerFunctor) : Typeω where
  open AnswerFunctor 𝒯
  field
    Ans-route : {ℓY ℓA ℓB : Level} {s : S} {Y : Type ℓY}
      (sY : isSet Y) (Φ : Y → TheorySet ℓA s)
      → Route (λ y → ty (Φ y)) ℓB → DiscreteEq Y
      → ty (&ᴰSet (λ y → Ans (Φ y))) ⊢ ty (Ans (⊕ᴰSet sY Φ))

module FromCov (𝒯 : AnswerFunctor) (cov : CovariantAnswer 𝒯) where
  open AnswerFunctor 𝒯
  open CovariantAnswer cov

  committing : CommittingAnswer 𝒯
  committing .CommittingAnswer.Ans-route {Y = Y} sY Φ R decY =
    ⊕ᴰ-elim step ∘⊢ &⊕ᴰ-distR
    ∘⊢ (id⊢ ,& (R .Route.cov .total ∘⊢ ⊤Ty-intro))
    where
    Ds : TheoryTy _ _
    Ds = ty (&ᴰSet (λ y → Ans (Φ y)))

    step : (v : Maybe Y) → Ds & R .Route.B v ⊢ ty (Ans (⊕ᴰSet sY Φ))
    step nothing = Ans-empty ∘⊢ ⊤Ty-intro
    step (just y₀) = Ans-fmap (σ⊕ y₀) ∘⊢ π y₀ ∘⊢ π₁

-- Ask every alternative of a finite sum, with no commitment.  `Dec` cannot
-- have it: `Ans-empty` is the base case.
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


module Combinators (𝒯 : AnswerFunctor)
  {X : Type ℓX} (xs : X → S) (O : LI.IPtOrder σeq V vs 𝒫 xs ℓ<) where

  open AnswerFunctor 𝒯 public
  open LI.GuardedIndexed σeq V vs 𝒫 xs O public

  Fam : (ℓA : Level) → Type _
  Fam ℓA = (x : X) → TheorySet ℓA (xs x)

  AnsFam : Fam ℓA → SetFam (ℓAns ℓA)
  AnsFam A = (λ x → ty (Ans (A x))) , λ x m → isSetTy (Ans (A x)) m

  Step : Fam ℓA → Type _
  Step A = ∀ x → ▷ (AnsFam A) x ⊢ ty (Ans (A x))

  Checker : Fam ℓA → Type _
  Checker A = ∀ x → ⊤Ty ⊢ ty (Ans (A x))

  fix : {A : Fam ℓA} → Step A → Checker A
  fix {A = A} φ = Fam▷.löb (AnsFam A .fst) (AnsFam A .snd) φ

  callAt : {A : Fam ℓA} (x' : X) {x : X} {m : ↓M (xs x)} {m' : ↓M (xs x')}
    → (x' , m') < (x , m) → ▷ (AnsFam A) x m → ty (Ans (A x')) m'
  callAt {A = A} x' lt β = ▷app (AnsFam A) lt β

  Ans-map : {s : S} {A : TheorySet ℓA s} {B : TheorySet ℓB s}
    → ty A ⊢ ty B → ty B ⊢ ty A → ty (Ans A) ⊢ ty (Ans B)
  Ans-map f g = Ans-map& (f ∘⊢ π₁) (g ∘⊢ π₁) ∘⊢ (id⊢ ,& ⊤Ty-intro)

  module _ {s : S} {D : TheoryTy ℓD s} where

    infixr 15 _<|>_

    _<|>_ : {A : TheorySet ℓA s} {B : TheorySet ℓB s}
      → D ⊢ ty (Ans A) → D ⊢ ty (Ans B) → D ⊢ ty (Ans (A ⊕Set B))
    (p <|> q) = Ans-⊕& ∘⊢ (p ,& q)

    side : {A : TheorySet ℓA s} → Decidable (ty A) → D ⊢ ty (Ans A)
    side d = Ans-ofDec ∘⊢ d ∘⊢ ⊤Ty-intro

    none : {A : TheorySet ℓA s} → (⊤Ty ⊢ ¬Ty (ty A)) → D ⊢ ty (Ans A)
    none n = side (dec-no ∘⊢ n)



-- A graded interface: answers pay a budget; survivors:
--
--     Ans-map&   cost unchanged, same `m`                  -- survives
--     Ans-ofDec  cost 1, and `1 ≤ k · size m`              -- survives
--     Ans-node   cost `1 + Σ`, and the slots are subterms  -- survives
--     Ans-⊕&     cost `c₁ + c₂`, both at the SAME `m`      -- dies
--     Ans-&&     cost `c₁ + c₂`, both at the SAME `m`      -- dies
--     Ans-re     cost 1 + c, at `f m`, and nothing relates
--                `size (f m)` to `size m`                  -- dies
--
-- No `k` absorbs the doubling.
record LinearAnswer : Typeω where
  field
    ℓAns : Level → Level
    Ans : {ℓA : Level} {s : S} → TheorySet ℓA s → TheorySet (ℓAns ℓA) s

    Ans-map& : {ℓA ℓB ℓH : Level} {s : S}
      {A : TheorySet ℓA s} {B : TheorySet ℓB s} {H : TheoryTy ℓH s}
      → ty A & H ⊢ ty B → ty B & H ⊢ ty A
      → ty (Ans A) & H ⊢ ty (Ans B)

    Ans-ofDec : {ℓA : Level} {s : S} {A : TheorySet ℓA s}
      → ty (DecSet A) ⊢ ty (Ans A)

    Ans-node : {ℓA : Level} (o : σ .ops) → Precise o
      → {As : NodeArgs ℓA o} {ms : interpIn o ↓M}
      → ((a : arities σ o) → ty (Ans (As ms a)) (ms a))
      → ty (Ans (⊗ᴰSet o As)) (op o ms)

-- Forgetting; the converse fails, and `Linear` says why.
linearOf : AnswerFunctor → LinearAnswer
linearOf 𝒯 .LinearAnswer.ℓAns = AnswerFunctor.ℓAns 𝒯
linearOf 𝒯 .LinearAnswer.Ans = AnswerFunctor.Ans 𝒯
linearOf 𝒯 .LinearAnswer.Ans-map& = AnswerFunctor.Ans-map& 𝒯
linearOf 𝒯 .LinearAnswer.Ans-ofDec = AnswerFunctor.Ans-ofDec 𝒯
linearOf 𝒯 .LinearAnswer.Ans-node = AnswerFunctor.Ans-node 𝒯

module LinearCombinators (𝒯 : LinearAnswer)
  {X : Type ℓX} (xs : X → S) (O : LI.IPtOrder σeq V vs 𝒫 xs ℓ<) where

  open LinearAnswer 𝒯 public
  open LI.GuardedIndexed σeq V vs 𝒫 xs O public

  Fam : (ℓA : Level) → Type _
  Fam ℓA = (x : X) → TheorySet ℓA (xs x)

  AnsFam : Fam ℓA → SetFam (ℓAns ℓA)
  AnsFam A = (λ x → ty (Ans (A x))) , λ x m → isSetTy (Ans (A x)) m

  Step : Fam ℓA → Type _
  Step A = ∀ x → ▷ (AnsFam A) x ⊢ ty (Ans (A x))

  Checker : Fam ℓA → Type _
  Checker A = ∀ x → ⊤Ty ⊢ ty (Ans (A x))

  fix : {A : Fam ℓA} → Step A → Checker A
  fix {A = A} φ = Fam▷.löb (AnsFam A .fst) (AnsFam A .snd) φ

  callAt : {A : Fam ℓA} (x' : X) {x : X} {m : ↓M (xs x)} {m' : ↓M (xs x')}
    → (x' , m') < (x , m) → ▷ (AnsFam A) x m → ty (Ans (A x')) m'
  callAt {A = A} x' lt β = ▷app (AnsFam A) lt β

  Ans-map : {s : S} {A : TheorySet ℓA s} {B : TheorySet ℓB s}
    → ty A ⊢ ty B → ty B ⊢ ty A → ty (Ans A) ⊢ ty (Ans B)
  Ans-map f g = Ans-map& (f ∘⊢ π₁) (g ∘⊢ π₁) ∘⊢ (id⊢ ,& ⊤Ty-intro)

  module _ {s : S} {D : TheoryTy ℓD s} where

    side : {A : TheorySet ℓA s} → Decidable (ty A) → D ⊢ ty (Ans A)
    side d = Ans-ofDec ∘⊢ d ∘⊢ ⊤Ty-intro

    none : {A : TheorySet ℓA s} → (⊤Ty ⊢ ¬Ty (ty A)) → D ⊢ ty (Ans A)
    none n = side (dec-no ∘⊢ n)
