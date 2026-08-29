{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A scope checker for untyped lambda terms, written once, for every answer.

   The family is indexed by the context, so `X = Ctx` and Löb is taken over
   contexts -- the analogue of "one nonterminal per production", except
   that the index is unbounded and that costs nothing, since `fix` asks
   nothing of `X`.

   The `lam` case is why `Core`'s node is `⊗ᴰ` and not `Operation/Base`'s
   `⊗ᵘ`: the body is checked in `ms zero ∷ Γ`, and `ms zero` is the *first
   slot's value*.  Independent slots cannot say that.

   Case analysis is `look` over `Guard`'s node cover, not a match on the
   term: `step` is `⊕ᴰ-elim` over the cover exactly as the monoid
   development's `look⊗` is `⊕ᴰ-elim` over the lookahead cover.  The cell
   `NodeAt o` is also what lets `unrollNode` be a `⊢`-term -- a grammar and
   one of its unfoldings agree only where the head is known, which is what
   `Ans-map&` carries.

   Nothing below mentions `Dec`, `Maybe` or `ND`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no)
open SortedSig
open SortedEqns
module Theory.Instances.Lambda.Scope
  (Name : Type ℓ-zero) (isSetName : isSet Name)
  (decName : (x y : Name) → Dec (x ≡ y))
  where

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool ; false≢true)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.List.Properties using (isOfHLevelList)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt ; Unit* ; tt*)
import Cubical.Data.Sum as Sum
open import Cubical.Data.Sum using (isProp⊎)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Lambda.Guard Name isSetName public
open import Theory.Type.Inductive.HLevels
  λEqns Name (λ _ → nm) termPresentation public

Ctx : Type ℓ-zero
Ctx = List Name

isSetCtx : isSet Ctx
isSetCtx = isOfHLevelList 0 isSetName

-- Membership, carrying the *position*.
--
-- The same proof-relevant refinement as `Annotated/Typing`'s `Lookup`: a
-- `Bool` test says only that the name is bound, whereas a chain of "not
-- here" steps ending in a hit says *where*, and counting the steps is the
-- de Bruijn index.  `Nameless` reads the converted term off a `Scope`
-- derivation rather than walking the context a second time.
--
-- Still a proposition -- the summands are mutually exclusive -- so
-- shadowing resolves inward and the index is unique.
InCtx : Ctx → TheoryTy ℓ-zero nm
InCtx [] x = Empty.⊥
InCtx (y ∷ Γ) x = (x ≡ y) Sum.⊎ ((x ≡ y → Empty.⊥) × InCtx Γ x)

deBruijn : (Γ : Ctx) (x : Name) → InCtx Γ x → ℕ
deBruijn (y ∷ Γ) x (Sum.inl _) = 0
deBruijn (y ∷ Γ) x (Sum.inr (_ , v)) = suc (deBruijn Γ x v)

private
  isPropNeq : {x y : Name} → isProp (x ≡ y → Empty.⊥)
  isPropNeq f g = funExt λ z → Empty.rec (f z)

isPropInCtx : (Γ : Ctx) (x : Name) → isProp (InCtx Γ x)
isPropInCtx [] x = λ ()
isPropInCtx (y ∷ Γ) x =
  isProp⊎ (isSetName _ _) (isProp× isPropNeq (isPropInCtx Γ x))
          (λ hit miss → miss .fst hit)

InCtxSet : Ctx → TheorySet ℓ-zero nm
InCtxSet Γ = InCtx Γ , λ x → isProp→isSet (isPropInCtx Γ x)

decInCtx : (Γ : Ctx) → Decidable (InCtx Γ)
decInCtx [] x _ = Sum.inr λ ()
decInCtx (y ∷ Γ) x _ = onName (decName x y)
  where
  onTail : (x ≡ y → Empty.⊥) → DecTy (InCtx Γ) x → DecTy (InCtx (y ∷ Γ)) x
  onTail ne (Sum.inl v) = Sum.inl (Sum.inr (ne , v))
  onTail ne (Sum.inr ¬v) = Sum.inr λ where
    (Sum.inl hit) → Empty.rec (ne hit)
    (Sum.inr miss) → ¬v (miss .snd)

  onName : Dec (x ≡ y) → DecTy (InCtx (y ∷ Γ)) x
  onName (yes p) = Sum.inl (Sum.inl p)
  onName (no ¬p) = onTail ¬p (decInCtx Γ x tt)

-- The grammar, as a `Functor` code.
--
-- `lamOp`'s body slot is `Var (ms theBinder ∷ Γ)`: an index computed from
-- slot zero's *value*, which is exactly what `⊗ᴰe` adds and what `⊗e`
-- cannot say.  So `Scope` is a `μ`, and `rollNode`/`unrollNode` below are
-- the `μ`'s own `roll`/`unroll` -- up to the summand tag and the `Lift`s
-- that `⟦ k A ⟧` and `⟦ Var x ⟧` insert.  See the note at the bottom of
-- this block for what that costs.
ScopeCode : LSort → Type (ℓ-suc ℓ-zero)
ScopeCode = Functor ℓ-zero Ctx (λ _ → tm)

-- The three productions, as the slots of their nodes.  This is `Slots`
-- below, read as codes rather than as grammars.
Rules : (Γ : Ctx) (o : LOp) (ms : interpIn o ↓M) → interpIn o ScopeCode
Rules Γ varOp ms theVar = k (InCtx Γ)
Rules Γ appOp ms a = Var Γ                 -- both slots alike, so no name
Rules Γ lamOp ms theBinder = k ⊤Ty
Rules Γ lamOp ms theBody = Var (ms theBinder ∷ Γ)

ScopeF : Ctx → ScopeCode tm
ScopeF Γ = ⊕e LOp λ o → ⊗ᴰe o (Rules Γ o)

isSetRules : (Γ : Ctx) (o : LOp) (ms : interpIn o ↓M) (a : arities λSig o)
  → isSetValued (Rules Γ o ms a)
isSetRules Γ varOp ms theVar = lift λ x → isProp→isSet (isPropInCtx Γ x)
isSetRules Γ appOp ms a = lift tt*
isSetRules Γ lamOp ms theBinder = lift isSet⊤Ty
isSetRules Γ lamOp ms theBody = lift tt*

isSetScopeF : (Γ : Ctx) → isSetValued (ScopeF Γ)
isSetScopeF Γ = lift isSetLOp , λ o ms a → isSetRules Γ o ms a

Scope : Ctx → TheoryTy (ℓ-suc ℓ-zero) tm
Scope = μ ScopeF

isSetScope : (Γ : Ctx) → isSetTheoryTy (Scope Γ)
isSetScope = isSetμ ScopeF isSetScopeF

ScopeSet : Ctx → TheorySet (ℓ-suc ℓ-zero) tm
ScopeSet Γ = Scope Γ , isSetScope Γ

-- `μ` lives one universe up -- `ℓF ℓ-zero` is `ℓ-suc ℓ-zero` -- and
-- `NodeArgs` is uniform in its level, so the two slots that are *not*
-- recursive have to be lifted to meet the ones that are.
LiftSet : {s : LSort} (ℓB : Level) → TheorySet ℓ-zero s → TheorySet ℓB s
LiftSet ℓB (A , sA) = LiftTheoryTy ℓB A , isSetLiftTheoryTy sA

-- The binder slot's "condition", named rather than written inline, so that
-- every slot of every rule below enters the answer the same way: through a
-- `Decidable` and `Ans-ofDec`.  This one happens to be trivially true --
-- the untyped calculus asks nothing of a bound name -- and saying so out
-- loud is cheaper than an exception to the convention.
dec⊤ : {s : LSort} → Decidable (LiftTheoryTy (ℓ-suc ℓ-zero) (⊤Ty {s = s}))
dec⊤ _ _ = Sum.inl (lift tt)

decInCtx↑ : (Γ : Ctx)
  → Decidable (LiftTheoryTy (ℓ-suc ℓ-zero) (InCtx Γ))
decInCtx↑ Γ = dec-retract liftTy lowerTy (decInCtx Γ)

Slots : (o : LOp) → Ctx → NodeArgs (ℓ-suc ℓ-zero) o
Slots varOp Γ ms theVar = LiftSet _ (InCtxSet Γ)
Slots appOp Γ ms a = ScopeSet Γ
Slots lamOp Γ ms theBinder = LiftSet _ (⊤Ty , isSet⊤Ty)
Slots lamOp Γ ms theBody = ScopeSet (ms theBinder ∷ Γ)

-- One level of unfolding, both ways, as `⊢`-terms.  `unrollNode` needs the
-- cell: a term is a node of `o` only where the cover says so.
--
-- These are `roll` and `unroll`, and the work that is left is bureaucracy
-- of two kinds.  (a) `⟦ Var x ⟧` is `Lift (μ ...)`, so every *recursive*
-- slot is wrapped and unwrapped; the two non-recursive slots need nothing,
-- since `Slots` already lifts them.  (b) `ScopeF` is a sum over LOp, so
-- `roll` needs the tag and `unroll` has to *find* it -- which is
-- no-confusion, i.e. exactly the cover's `disjoint` field.
rollNode : (o : LOp) (Γ : Ctx) → ⊗ᴰ o (Slots o Γ) ⊢ Scope Γ
rollNode varOp Γ m (ms , e , ws) =
  roll m (varOp , ms , e , λ where theVar → ws theVar)
rollNode appOp Γ m (ms , e , ws) = roll m (appOp , ms , e , λ a → lift (ws a))
rollNode lamOp Γ m (ms , e , ws) = roll m (lamOp , ms , e , λ where
  theBinder → ws theBinder
  theBody → lift (ws theBody))

private
  -- no-confusion, in the form the summand selection wants
  noConf : (o o' : LOp) → (o Eq.≡ o' → Empty.⊥) → (m : RawTm)
    → NodeAt o m → NodeAt o' m → Empty.⊥
  noConf o o' ne m nd nd' =
    Empty.rec* (nodeCover .disjoint o o' ne m (nd , nd'))

  -- `μ` sums over *every* operation; the cover cell says which summand a
  -- given node is in.  Three of the nine cases do the `Lift` bookkeeping;
  -- the other six are the refutation above.
  atHead : (Γ : Ctx) (o o' : LOp) (m : RawTm) → NodeAt o m
    → ⟦ ⊗ᴰe o' (Rules Γ o') ⟧TheoryTy Scope m
    → ⊗ᴰ o (Slots o Γ) m
  atHead Γ varOp varOp m nd (ms , e , ws) =
    ms , e , λ where theVar → ws theVar
  atHead Γ appOp appOp m nd (ms , e , ws) = ms , e , λ a → ws a .lower
  atHead Γ lamOp lamOp m nd (ms , e , ws) = ms , e , λ where
    theBinder → ws theBinder
    theBody → ws theBody .lower
  atHead Γ varOp appOp m nd x =
    Empty.rec (noConf varOp appOp (λ ()) m nd (x .fst , x .snd .fst))
  atHead Γ varOp lamOp m nd x =
    Empty.rec (noConf varOp lamOp (λ ()) m nd (x .fst , x .snd .fst))
  atHead Γ appOp varOp m nd x =
    Empty.rec (noConf appOp varOp (λ ()) m nd (x .fst , x .snd .fst))
  atHead Γ appOp lamOp m nd x =
    Empty.rec (noConf appOp lamOp (λ ()) m nd (x .fst , x .snd .fst))
  atHead Γ lamOp varOp m nd x =
    Empty.rec (noConf lamOp varOp (λ ()) m nd (x .fst , x .snd .fst))
  atHead Γ lamOp appOp m nd x =
    Empty.rec (noConf lamOp appOp (λ ()) m nd (x .fst , x .snd .fst))

unrollNode : (o : LOp) (Γ : Ctx) → Scope Γ & NodeAt o ⊢ ⊗ᴰ o (Slots o Γ)
unrollNode o Γ m (s , nd) =
  atHead Γ o (unroll ScopeF Γ m s .fst) m nd (unroll ScopeF Γ m s .snd)


-- The checker, for whatever answer.
module Check (𝒯 : AnswerFunctor) where

  open Subterm {X = Ctx} isSetCtx (λ _ → 0) hiding (_<_) public
  open Combinators 𝒯 srt order public

  step : Step ScopeSet
  step Γ = look nodeCover branch
    where
    -- the answer at the node the cell names
    nodeAns : (o : LOp)
      → ▷ (AnsFam ScopeSet) Γ & NodeAt o ⊢ ty (Ans (⊗ᴰSet o (Slots o Γ)))
    nodeAns varOp m (β , (ms , Eq.refl)) =
      Ans-node varOp (preciseλ varOp) {As = Slots varOp Γ} {ms = ms}
        λ where theVar → Ans-ofDec (ms theVar) (decInCtx↑ Γ (ms theVar) tt)
    nodeAns appOp m (β , (ms , Eq.refl)) =
      Ans-node appOp (preciseλ appOp) {As = Slots appOp Γ} {ms = ms}
        λ where
          theFun → callAt Γ
            (callFun {x = Γ} {x' = Γ} (ms theFun) (ms theArg)) β
          theArg → callAt Γ
            (callArg {x = Γ} {x' = Γ} (ms theFun) (ms theArg)) β
    nodeAns lamOp m (β , (ms , Eq.refl)) =
      Ans-node lamOp (preciseλ lamOp) {As = Slots lamOp Γ} {ms = ms}
        λ where
          theBinder → Ans-ofDec (ms theBinder) (dec⊤ (ms theBinder) tt)
          theBody → callAt (ms theBinder ∷ Γ)
            (callBody {x = Γ} {x' = ms theBinder ∷ Γ}
              (ms theBinder) (ms theBody)) β

    branch : (o : LOp)
      → ▷ (AnsFam ScopeSet) Γ & NodeAt o ⊢ ty (Ans (ScopeSet Γ))
    branch o =
      Ans-map& (rollNode o Γ ∘⊢ π₁) (unrollNode o Γ) ∘⊢ (nodeAns o ,& π₂)

  scoped : Checker ScopeSet
  scoped = fix step
