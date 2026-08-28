{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A scope checker for untyped lambda terms, written once, for every answer.

   The family is indexed by the context, so `X = Ctx` and Löb is taken at
   `&ᴰ` over contexts -- the analogue of "one nonterminal per production" in
   the monoid development, except that here the index is unbounded and that
   costs nothing, since `FixAll`/`fix` asks nothing of `X`.

   The `lam` case is why `Core`'s node is `⊗ᴰ` and not `Operation/Base`'s
   `⊗ᵘ`: the body is checked in `ms zero ∷ Γ`, and `ms zero` is the *first
   slot's value*.  Independent slots cannot say that, so a binder is
   literally unstateable with `⊗ᵘ`.  With the dependency it is one line.

   Nothing below mentions `Dec`, `Maybe` or `ND`.  `Check` takes the answer
   as a parameter; `ScopeTests` instantiates it three ways. -}
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

-- ...as a grammar at sort `nm`: a predicate on names.
InCtx : Ctx → TheoryTy ℓ-zero nm
InCtx Γ x = memB x Γ ≡ true

InCtxSet : Ctx → TheorySet ℓ-zero nm
InCtxSet Γ = InCtx Γ , λ x → isProp→isSet (isSetBool _ _)

decInCtx : (Γ : Ctx) (x : Name)
  → InCtx Γ x Sum.⊎ (InCtx Γ x → Empty.⊥)
decInCtx Γ x = onB (memB x Γ)
  where
  onB : (b : Bool) → (b ≡ true) Sum.⊎ ((b ≡ true) → Empty.⊥)
  onB true = Sum.inl refl
  onB false = Sum.inr false≢true

-- The grammar.  Defined by recursion on the term, so it is a *proposition*
-- -- being in scope has no content beyond holding -- and `unambiguous` comes
-- for free rather than as a theorem.
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

-- The three productions, as nodes.  Only `LamSlots` uses the dependency on
-- the splitting -- and it is the whole reason `⊗ᴰ` exists.
VarSlots : Ctx → NodeArgs ℓ-zero varOp
VarSlots Γ ms a = InCtxSet Γ

AppSlots : Ctx → NodeArgs ℓ-zero appOp
AppSlots Γ ms a = ScopeSet Γ

LamSlots : Ctx → NodeArgs ℓ-zero lamOp
LamSlots Γ ms zero = ⊤Set
LamSlots Γ ms (suc zero) = ScopeSet (ms zero ∷ Γ)

ScopeBody : Ctx → TheorySet ℓ-zero tm
ScopeBody Γ =
  ⊗ᴰSet varOp (VarSlots Γ)
    ⊕Set (⊗ᴰSet appOp (AppSlots Γ) ⊕Set ⊗ᴰSet lamOp (LamSlots Γ))

-- One level of unfolding, and its inverse.  This is the `roll`/`unroll`
-- pair every grammar in `Combinator/Grammars` supplies; here the sum is
-- over head constructors rather than over production tags.
unrollScope : (Γ : Ctx) → Scope Γ ⊢ ty (ScopeBody Γ)
unrollScope Γ (tvar x) s = Sum.inl (node-mk {ms = λ _ → x} λ _ → s)
unrollScope Γ (tapp t u) s =
  Sum.inr (Sum.inl (node-mk {ms = appArgs t u} λ where
    zero → s .fst
    (suc zero) → s .snd))
unrollScope Γ (tlam x t) s =
  Sum.inr (Sum.inr (node-mk {ms = lamArgs x t} λ where
    zero → tt
    (suc zero) → s))

rollScope : (Γ : Ctx) → ty (ScopeBody Γ) ⊢ Scope Γ
rollScope Γ m (Sum.inl (ms , Eq.refl , ws)) = ws zero
rollScope Γ m (Sum.inr (Sum.inl (ms , Eq.refl , ws))) = ws zero , ws (suc zero)
rollScope Γ m (Sum.inr (Sum.inr (ms , Eq.refl , ws))) = ws (suc zero)


-- The checker, for whatever answer.
module Check (𝒯 : AnswerFunctor) where

  open Subterm {X = Ctx} isSetCtx (λ _ → 0) hiding (_<_) public
  open Combinators 𝒯 srt order public

  private
    -- the branches not taken: a node whose operation is not the term's head
    clash : (o : LOp) (As : NodeArgs ℓ-zero o) (m : RawTm)
      → (HdCode (hdOfOp o) (hdOf m) → Empty.⊥)
      → ty (Ans (⊗ᴰSet o As)) m
    clash o As m ne =
      Ans-dec (Sum.inr λ z → headClash o m ne (z .fst) (z .snd .fst))

  step : Step ScopeSet
  step Γ (tvar x) β =
    Ans-map (rollScope Γ) (unrollScope Γ) (tvar x)
      (Ans-⊕& (tvar x) (hit , Ans-⊕& (tvar x)
        ( clash appOp (AppSlots Γ) (tvar x) (λ z → z)
        , clash lamOp (LamSlots Γ) (tvar x) (λ z → z) )))
    where
    hit : ty (Ans (⊗ᴰSet varOp (VarSlots Γ))) (tvar x)
    hit = Ans-node varOp (preciseλ varOp) {As = VarSlots Γ} {ms = λ _ → x}
      λ _ → Ans-dec (decInCtx Γ x)
  step Γ (tapp t u) β =
    Ans-map (rollScope Γ) (unrollScope Γ) (tapp t u)
      (Ans-⊕& (tapp t u)
        ( clash varOp (VarSlots Γ) (tapp t u) (λ z → z)
        , Ans-⊕& (tapp t u)
            (hit , clash lamOp (LamSlots Γ) (tapp t u) (λ z → z))))
    where
    hit : ty (Ans (⊗ᴰSet appOp (AppSlots Γ))) (tapp t u)
    hit = Ans-node appOp (preciseλ appOp) {As = AppSlots Γ} {ms = appArgs t u}
      λ where
        zero → callAt Γ (callFun {x = Γ} {x' = Γ} t u) β
        (suc zero) → callAt Γ (callArg {x = Γ} {x' = Γ} t u) β
  step Γ (tlam x t) β =
    Ans-map (rollScope Γ) (unrollScope Γ) (tlam x t)
      (Ans-⊕& (tlam x t)
        ( clash varOp (VarSlots Γ) (tlam x t) (λ z → z)
        , Ans-⊕& (tlam x t)
            (clash appOp (AppSlots Γ) (tlam x t) (λ z → z) , hit)))
    where
    hit : ty (Ans (⊗ᴰSet lamOp (LamSlots Γ))) (tlam x t)
    hit = Ans-node lamOp (preciseλ lamOp) {As = LamSlots Γ} {ms = lamArgs x t}
      λ where
        zero → Ans-dec (Sum.inl tt)
        (suc zero) → callAt (x ∷ Γ) (callBody {x = Γ} {x' = x ∷ Γ} x t) β

  scoped : Checker ScopeSet
  scoped = fix step
