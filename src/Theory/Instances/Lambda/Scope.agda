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
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Sum as Sum
open import Cubical.Data.Sum using (isProp⊎)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Lambda.Guard Name isSetName public

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

-- The grammar.  A proposition, so `unambiguous` is definitional.
Scope : Ctx → TheoryTy ℓ-zero tm
Scope Γ (tvar x) = InCtx Γ x
Scope Γ (tapp t u) = Scope Γ t × Scope Γ u
Scope Γ (tlam x t) = Scope (x ∷ Γ) t

isPropScope : (Γ : Ctx) (t : RawTm) → isProp (Scope Γ t)
isPropScope Γ (tvar x) = isPropInCtx Γ x
isPropScope Γ (tapp t u) = isProp× (isPropScope Γ t) (isPropScope Γ u)
isPropScope Γ (tlam x t) = isPropScope (x ∷ Γ) t

ScopeSet : Ctx → TheorySet ℓ-zero tm
ScopeSet Γ = Scope Γ , λ t → isProp→isSet (isPropScope Γ t)

⊤Set : {s : LSort} → TheorySet ℓ-zero s
⊤Set = ⊤Ty , isSet⊤Ty

-- The binder slot's "condition", named rather than written inline, so that
-- every slot of every rule below enters the answer the same way: through a
-- `Decidable` and `Ans-ofDec`.  This one happens to be trivially true --
-- the untyped calculus asks nothing of a bound name -- and saying so out
-- loud is cheaper than an exception to the convention.
dec⊤ : {s : LSort} → Decidable (⊤Ty {s = s})
dec⊤ _ _ = Sum.inl tt

-- The three productions, as the slots of their nodes.  Only `lamOp` uses
-- the dependency on the splitting, and it is the whole reason for `⊗ᴰ`.
Slots : (o : LOp) → Ctx → NodeArgs ℓ-zero o
Slots varOp Γ ms theVar = InCtxSet Γ
Slots appOp Γ ms a = ScopeSet Γ            -- both slots alike, so no name
Slots lamOp Γ ms theBinder = ⊤Set
Slots lamOp Γ ms theBody = ScopeSet (ms theBinder ∷ Γ)

-- One level of unfolding, both ways, as `⊢`-terms.  `unrollNode` needs the
-- cell: a term is a node of `o` only where the cover says so.
rollNode : (o : LOp) (Γ : Ctx) → ⊗ᴰ o (Slots o Γ) ⊢ Scope Γ
rollNode varOp Γ m (ms , Eq.refl , ws) = ws theVar
rollNode appOp Γ m (ms , Eq.refl , ws) = ws theFun , ws theArg
rollNode lamOp Γ m (ms , Eq.refl , ws) = ws theBody

unrollNode : (o : LOp) (Γ : Ctx) → Scope Γ & NodeAt o ⊢ ⊗ᴰ o (Slots o Γ)
unrollNode varOp Γ m (s , (ms , Eq.refl)) =
  node-mk {ms = ms} λ where theVar → s
unrollNode appOp Γ m (s , (ms , Eq.refl)) =
  node-mk {ms = ms} λ where
    theFun → s .fst
    theArg → s .snd
unrollNode lamOp Γ m (s , (ms , Eq.refl)) =
  node-mk {ms = ms} λ where
    theBinder → tt
    theBody → s


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
        λ where theVar → Ans-ofDec (ms theVar) (decInCtx Γ (ms theVar) tt)
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
