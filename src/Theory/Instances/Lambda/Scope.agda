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
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.List.Properties using (isOfHLevelList)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Lambda.Guard Name isSetName public

Ctx : Type ℓ-zero
Ctx = List Name

isSetCtx : isSet Ctx
isSetCtx = isOfHLevelList 0 isSetName

-- Membership, as a `Bool` so that it is a proposition and decidable at once.
memB : Name → Ctx → Bool
memB x [] = false
memB x (y ∷ Γ) = onEq (decName x y)
  where
  onEq : Dec (x ≡ y) → Bool
  onEq (yes _) = true
  onEq (no _) = memB x Γ

-- ...as a grammar at sort `nm`, and as a decision the answer can read.
InCtx : Ctx → TheoryTy ℓ-zero nm
InCtx Γ x = memB x Γ ≡ true

InCtxSet : Ctx → TheorySet ℓ-zero nm
InCtxSet Γ = InCtx Γ , λ x → isProp→isSet (isSetBool _ _)

decInCtx : (Γ : Ctx) → Decidable (InCtx Γ)
decInCtx Γ x _ = onB (memB x Γ)
  where
  onB : (b : Bool) → (b ≡ true) Sum.⊎ ((b ≡ true) → ⊥Ty x)
  onB true = Sum.inl refl
  onB false = Sum.inr λ p → Empty.rec (false≢true p)

-- The grammar.  A proposition, so `unambiguous` is definitional.
Scope : Ctx → TheoryTy ℓ-zero tm
Scope Γ (tvar x) = InCtx Γ x
Scope Γ (tapp t u) = Scope Γ t × Scope Γ u
Scope Γ (tlam x t) = Scope (x ∷ Γ) t

isPropScope : (Γ : Ctx) (t : RawTm) → isProp (Scope Γ t)
isPropScope Γ (tvar x) = isSetBool _ _
isPropScope Γ (tapp t u) = isProp× (isPropScope Γ t) (isPropScope Γ u)
isPropScope Γ (tlam x t) = isPropScope (x ∷ Γ) t

ScopeSet : Ctx → TheorySet ℓ-zero tm
ScopeSet Γ = Scope Γ , λ t → isProp→isSet (isPropScope Γ t)

⊤Set : {s : LSort} → TheorySet ℓ-zero s
⊤Set = ⊤Ty , isSet⊤Ty

-- The three productions, as the slots of their nodes.  Only `lamOp` uses
-- the dependency on the splitting, and it is the whole reason for `⊗ᴰ`.
Slots : (o : LOp) → Ctx → NodeArgs ℓ-zero o
Slots varOp Γ ms a = InCtxSet Γ
Slots appOp Γ ms a = ScopeSet Γ
Slots lamOp Γ ms zero = ⊤Set
Slots lamOp Γ ms (suc zero) = ScopeSet (ms zero ∷ Γ)

-- One level of unfolding, both ways, as `⊢`-terms.  `unrollNode` needs the
-- cell: a term is a node of `o` only where the cover says so.
rollNode : (o : LOp) (Γ : Ctx) → ⊗ᴰ o (Slots o Γ) ⊢ Scope Γ
rollNode varOp Γ m (ms , Eq.refl , ws) = ws zero
rollNode appOp Γ m (ms , Eq.refl , ws) = ws zero , ws (suc zero)
rollNode lamOp Γ m (ms , Eq.refl , ws) = ws (suc zero)

unrollNode : (o : LOp) (Γ : Ctx) → Scope Γ & NodeAt o ⊢ ⊗ᴰ o (Slots o Γ)
unrollNode varOp Γ m (s , (ms , Eq.refl)) =
  node-mk {ms = ms} λ where zero → s
unrollNode appOp Γ m (s , (ms , Eq.refl)) =
  node-mk {ms = ms} λ where
    zero → s .fst
    (suc zero) → s .snd
unrollNode lamOp Γ m (s , (ms , Eq.refl)) =
  node-mk {ms = ms} λ where
    zero → tt
    (suc zero) → s


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
        λ where zero → Ans-ofDec (ms zero) (decInCtx Γ (ms zero) tt)
    nodeAns appOp m (β , (ms , Eq.refl)) =
      Ans-node appOp (preciseλ appOp) {As = Slots appOp Γ} {ms = ms}
        λ where
          zero → callAt Γ
            (callFun {x = Γ} {x' = Γ} (ms zero) (ms (suc zero))) β
          (suc zero) → callAt Γ
            (callArg {x = Γ} {x' = Γ} (ms zero) (ms (suc zero))) β
    nodeAns lamOp m (β , (ms , Eq.refl)) =
      Ans-node lamOp (preciseλ lamOp) {As = Slots lamOp Γ} {ms = ms}
        λ where
          zero → Ans-ofDec (ms zero) (Sum.inl tt)
          (suc zero) → callAt (ms zero ∷ Γ)
            (callBody {x = Γ} {x' = ms zero ∷ Γ} (ms zero) (ms (suc zero))) β

    branch : (o : LOp)
      → ▷ (AnsFam ScopeSet) Γ & NodeAt o ⊢ ty (Ans (ScopeSet Γ))
    branch o =
      Ans-map& (rollNode o Γ ∘⊢ π₁) (unrollNode o Γ) ∘⊢ (nodeAns o ,& π₂)

  scoped : Checker ScopeSet
  scoped = fix step
