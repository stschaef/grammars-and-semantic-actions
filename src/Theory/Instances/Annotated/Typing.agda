{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A type checker for the annotated lambda calculus, written once, for
   every answer.

   The family is indexed by `Ctx × Ty` -- a checking judgment `Γ ⊢ t ⇐ A`
   -- and the guard descends on the term.  Each rule's premises are at
   indices computed from the conclusion's index and the node's own data,
   which is exactly what `Core`'s dependent node `⊗ᴰ` provides:

     var        the slot is the side condition `Γ(x) = A`
     app[B]     slot 0 at `Γ ⊢ ⇐ B ⇒ A`, slot 1 at `Γ ⊢ ⇐ B`
     lam[B]     slot 0 is the side condition `A = B ⇒ _`,
                slot 1 at `(x,B),Γ ⊢ ⇐ cod A`, where `x` is slot 0's value

   The `lam` rule uses the dependency twice over: the body's *context* and
   its *type* are both read off the node.  With `Operation/Base`'s `⊗ᵘ` --
   independent slots -- neither is expressible.

   Why the application carries `B`.  Drop it and the rule becomes

     Γ ⊢ f a ⇐ A   iff   ∃B. Γ ⊢ f ⇐ B ⇒ A  and  Γ ⊢ a ⇐ B

   an existential over an infinite index.  Deciding that is precisely what
   `Theory/Type/Decidable/Route`'s `routeIn` is for -- a cover of the
   alternatives, `total` saying every term synthesises a type or provably
   none, `disjoint` saying the synthesised type is unique.  In other words
   the annotation buys exactly the bidirectional discipline, and without it
   a checker owes uniqueness-of-synthesis as a side theorem.  That is the
   honest boundary of what these combinators do for you.

   Nothing below mentions `Dec`, `Maybe` or `ND`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Annotated.Typing where

open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.List.Properties using (isOfHLevelList)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Maybe.Properties using (isOfHLevelMaybe ; discreteMaybe)
open import Cubical.Data.Nat using (ℕ ; isSetℕ ; discreteℕ)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd ; ΣPathP)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Annotated.Guard public

-- Contexts and lookup.
Ctx : Type ℓ-zero
Ctx = List (ℕ × Ty)

isSetCtx : isSet Ctx
isSetCtx = isOfHLevelList 0 (isSetΣ isSetℕ λ _ → isSetTyp)

lookC : Ctx → ℕ → Maybe Ty
lookC [] x = nothing
lookC ((y , A) ∷ Γ) x = onEq (discreteℕ x y)
  where
  onEq : Dec (x ≡ y) → Maybe Ty
  onEq (yes _) = just A
  onEq (no _) = lookC Γ x

-- The index: a context and the type being checked against.
Idx : Type ℓ-zero
Idx = Ctx × Ty

isSetIdx : isSet Idx
isSetIdx = isSetΣ isSetCtx λ _ → isSetTyp

-- "A is an arrow with domain B", the `lam` rule's side condition.
ArrHead : Ty → Ty → Type ℓ-zero
ArrHead A B = IsArr A × (dom A ≡ B)

isPropArrHead : (A B : Ty) → isProp (ArrHead A B)
isPropArrHead A B = isProp× (isPropIsArr A) (isSetTyp _ _)

decArrHead : (A B : Ty) → ArrHead A B Sum.⊎ (ArrHead A B → Empty.⊥)
decArrHead ι B = Sum.inr λ z → z .fst
decArrHead (B' ⇒ C) B = onDom (discreteTy B' B)
  where
  onDom : Dec (B' ≡ B) → ArrHead (B' ⇒ C) B Sum.⊎ (ArrHead (B' ⇒ C) B → Empty.⊥)
  onDom (yes p) = Sum.inl (tt , p)
  onDom (no ¬p) = Sum.inr λ z → ¬p (z .snd)

-- ...and the `var` rule's.
Look : Ctx → Ty → TheoryTy ℓ-zero nm
Look Γ A x = lookC Γ x ≡ just A

LookSet : Ctx → Ty → TheorySet ℓ-zero nm
LookSet Γ A = Look Γ A , λ x → isProp→isSet (isOfHLevelMaybe 0 isSetTyp _ _)

decLook : (Γ : Ctx) (A : Ty) (x : ℕ)
  → Look Γ A x Sum.⊎ (Look Γ A x → Empty.⊥)
decLook Γ A x = onEq (discreteMaybe discreteTy (lookC Γ x) (just A))
  where
  onEq : Dec (lookC Γ x ≡ just A)
    → Look Γ A x Sum.⊎ (Look Γ A x → Empty.⊥)
  onEq (yes p) = Sum.inl p
  onEq (no ¬p) = Sum.inr ¬p

-- The judgment, by recursion on the term.  Every premise's index is
-- determined, so this is a proposition: a well-typed term has exactly one
-- derivation, and `unambiguous` is definitional rather than a theorem.
Der : Idx → TheoryTy ℓ-zero tm
Der (Γ , A) (avar x) = Look Γ A x
Der (Γ , A) (aapp B f a) = Der (Γ , B ⇒ A) f × Der (Γ , B) a
Der (Γ , A) (alam x B t) = ArrHead A B × Der ((x , B) ∷ Γ , cod A) t

isPropDer : (i : Idx) (t : ATm) → isProp (Der i t)
isPropDer (Γ , A) (avar x) = isOfHLevelMaybe 0 isSetTyp _ _
isPropDer (Γ , A) (aapp B f a) =
  isProp× (isPropDer (Γ , B ⇒ A) f) (isPropDer (Γ , B) a)
isPropDer (Γ , A) (alam x B t) =
  isProp× (isPropArrHead A B) (isPropDer ((x , B) ∷ Γ , cod A) t)

DerSet : Idx → TheorySet ℓ-zero tm
DerSet i = Der i , λ t → isProp→isSet (isPropDer i t)

-- The three rules, as nodes.
VarSlots : Idx → NodeArgs ℓ-zero varOp
VarSlots (Γ , A) ms a = LookSet Γ A

AppSlots : (B : Ty) (i : Idx) → NodeArgs ℓ-zero (appOp B)
AppSlots B (Γ , A) ms zero = DerSet (Γ , B ⇒ A)
AppSlots B (Γ , A) ms (suc zero) = DerSet (Γ , B)

ArrSet : Ty → Ty → TheorySet ℓ-zero nm
ArrSet A B = (λ _ → ArrHead A B) , λ _ → isProp→isSet (isPropArrHead A B)

LamSlots : (B : Ty) (i : Idx) → NodeArgs ℓ-zero (lamOp B)
LamSlots B (Γ , A) ms zero = ArrSet A B
LamSlots B (Γ , A) ms (suc zero) = DerSet ((ms zero , B) ∷ Γ , cod A)

-- Argument tuples, once.
appArgs : (B : Ty) → ATm → ATm → (b : Fin 2) → ↓M (SortOf (appOp B) b)
appArgs B u v zero = u
appArgs B u v (suc zero) = v

lamArgs : (B : Ty) → ℕ → ATm → (b : Fin 2) → ↓M (SortOf (lamOp B) b)
lamArgs B y u zero = y
lamArgs B y u (suc zero) = u

-- One level of unfolding, at the term in hand.  Pointwise, because the
-- operation is chosen by the term -- there is no finite sum to roll into.
rollVar : (Γ : Ctx) (A : Ty) (x : ℕ)
  → ty (⊗ᴰSet varOp (VarSlots (Γ , A))) (avar x) → Der (Γ , A) (avar x)
rollVar Γ A x (ms , Eq.refl , ws) = ws zero

unrollVar : (Γ : Ctx) (A : Ty) (x : ℕ)
  → Der (Γ , A) (avar x) → ty (⊗ᴰSet varOp (VarSlots (Γ , A))) (avar x)
unrollVar Γ A x d = node-mk {ms = λ _ → x} λ _ → d

rollApp : (Γ : Ctx) (A B : Ty) (f a : ATm)
  → ty (⊗ᴰSet (appOp B) (AppSlots B (Γ , A))) (aapp B f a)
  → Der (Γ , A) (aapp B f a)
rollApp Γ A B f a (ms , e , ws) =
    subst (Der (Γ , B ⇒ A)) fEq (ws zero)
  , subst (Der (Γ , B)) aEq (ws (suc zero))
  where
  whole : aapp B (ms zero) (ms (suc zero)) ≡ aapp B f a
  whole = Eq.eqToPath e

  fEq : ms zero ≡ f
  fEq = cong appFun whole

  aEq : ms (suc zero) ≡ a
  aEq = cong appArgOf whole

unrollApp : (Γ : Ctx) (A B : Ty) (f a : ATm)
  → Der (Γ , A) (aapp B f a)
  → ty (⊗ᴰSet (appOp B) (AppSlots B (Γ , A))) (aapp B f a)
unrollApp Γ A B f a d = node-mk {ms = appArgs B f a} λ where
  zero → d .fst
  (suc zero) → d .snd

rollLam : (Γ : Ctx) (A B : Ty) (x : ℕ) (t : ATm)
  → ty (⊗ᴰSet (lamOp B) (LamSlots B (Γ , A))) (alam x B t)
  → Der (Γ , A) (alam x B t)
rollLam Γ A B x t (ms , e , ws) =
  ws zero , subst mot (ΣPathP (xEq , tEq)) (ws (suc zero))
  where
  whole : alam (ms zero) B (ms (suc zero)) ≡ alam x B t
  whole = Eq.eqToPath e

  xEq : ms zero ≡ x
  xEq = cong (lamN (ms zero)) whole

  tEq : ms (suc zero) ≡ t
  tEq = cong lamBd whole

  mot : ℕ × ATm → Type ℓ-zero
  mot p = Der ((p .fst , B) ∷ Γ , cod A) (p .snd)

unrollLam : (Γ : Ctx) (A B : Ty) (x : ℕ) (t : ATm)
  → Der (Γ , A) (alam x B t)
  → ty (⊗ᴰSet (lamOp B) (LamSlots B (Γ , A))) (alam x B t)
unrollLam Γ A B x t d = node-mk {ms = lamArgs B x t} λ where
  zero → d .fst
  (suc zero) → d .snd


-- The checker, for whatever answer.
module Check (𝒯 : AnswerFunctor) where

  open Subterm {X = Idx} isSetIdx (λ _ → 0) hiding (_<_) public
  open Combinators 𝒯 srt order public

  step : Step DerSet
  step (Γ , A) (avar x) β =
    Ans-mapAt (rollVar Γ A x) (unrollVar Γ A x)
      (Ans-node varOp (preciseA varOp) {As = VarSlots (Γ , A)} {ms = λ _ → x}
        λ _ → Ans-dec (decLook Γ A x))
  step (Γ , A) (aapp B f a) β =
    Ans-mapAt (rollApp Γ A B f a) (unrollApp Γ A B f a)
      (Ans-node (appOp B) (preciseA (appOp B))
        {As = AppSlots B (Γ , A)} {ms = appArgs B f a}
        λ where
          zero → callAt (Γ , B ⇒ A)
            (callFun {x = Γ , A} {x' = Γ , B ⇒ A} B f a) β
          (suc zero) → callAt (Γ , B)
            (callArg {x = Γ , A} {x' = Γ , B} B f a) β)
  step (Γ , A) (alam x B t) β =
    Ans-mapAt (rollLam Γ A B x t) (unrollLam Γ A B x t)
      (Ans-node (lamOp B) (preciseA (lamOp B))
        {As = LamSlots B (Γ , A)} {ms = lamArgs B x t}
        λ where
          zero → Ans-dec (decArrHead A B)
          (suc zero) → callAt ((x , B) ∷ Γ , cod A)
            (callBody {x = Γ , A} {x' = (x , B) ∷ Γ , cod A} x B t) β)

  typed : Checker DerSet
  typed = fix step
