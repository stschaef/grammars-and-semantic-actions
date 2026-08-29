{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A type checker for the annotated lambda calculus, written once, for
   every answer.

   The family is indexed by `Ctx × Ty` -- a checking judgment `Γ ⊢ t ⇐ A`
   -- and the guard descends on the term.  Each rule's premises sit at
   indices computed from the conclusion's index and the node's own data,
   which is what `Core`'s dependent node `⊗ᴰ` provides:

     var        the slot is the side condition `Γ(x) = A`
     app[B]     slot 0 at `Γ ⊢ ⇐ B ⇒ A`, slot 1 at `Γ ⊢ ⇐ B`
     lam[B]     slot 0 is the side condition `A = B ⇒ _`,
                slot 1 at `(x,B),Γ ⊢ ⇐ cod A`, where `x` is slot 0's value

   The `lam` rule uses the dependency twice over: the body's *context* and
   its *type* are both read off the node.  With `Operation/Base`'s `⊗ᵘ` --
   independent slots -- neither is expressible.

   `AOp` is infinite, since `appOp B` carries a type.  That costs nothing:
   `Guard`'s node cover is a `Cover` over it all the same, and `step` is
   `look` over that cover.  What an infinite index *would* cost is a sum
   over the cells, and `Ans-map&` is what avoids it -- the relabelling is
   conditioned on the cell rather than being a map into `⊕ᴰ AOp`.

   Why the application carries `B`.  Drop it and the rule becomes

     Γ ⊢ f a ⇐ A   iff   ∃B. Γ ⊢ f ⇐ B ⇒ A  and  Γ ⊢ a ⇐ B

   an existential over an infinite index -- and now it is a sum over the
   cells, which is what `Theory/Type/Decidable/Route`'s `routeIn` is for:
   `total` says every term synthesises a type or provably none, `disjoint`
   says the synthesised type is unique.  The annotation buys exactly the
   bidirectional discipline; without it a checker owes uniqueness of
   synthesis as a side theorem.  That is the honest boundary.

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
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no)
import Cubical.Data.Sum as Sum
open import Cubical.Data.Sum using (isProp⊎)
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
Jdg : Type ℓ-zero
Jdg = Ctx × Ty

isSetIdx : isSet Jdg
isSetIdx = isSetΣ isSetCtx λ _ → isSetTyp

-- The `lam` rule's side condition: "A is an arrow with domain B".
ArrHead : Ty → Ty → Type ℓ-zero
ArrHead A B = IsArr A × (dom A ≡ B)

isPropArrHead : (A B : Ty) → isProp (ArrHead A B)
isPropArrHead A B = isProp× (isPropIsArr A) (isSetTyp _ _)

ArrSet : Ty → Ty → TheorySet ℓ-zero nm
ArrSet A B = (λ _ → ArrHead A B) , λ _ → isProp→isSet (isPropArrHead A B)

decArrHead : (A B : Ty) → Decidable (ty (ArrSet A B))
decArrHead ι B x _ = Sum.inr λ z → Empty.rec (z .fst)
decArrHead (B' ⇒ C) B x _ = onDom (discreteTy B' B)
  where
  onDom : Dec (B' ≡ B) → DecTy (ty (ArrSet (B' ⇒ C) B)) x
  onDom (yes p) = Sum.inl (tt , p)
  onDom (no ¬p) = Sum.inr λ z → Empty.rec (¬p (z .snd))

-- The `var` rule's premise, carrying the *position*.
--
-- This is the proof-relevant refinement.  `lookC Γ x ≡ just A` said only
-- that lookup succeeds; `Lookup Γ A x` is the witness that it does -- a
-- chain of "not here" steps ending in a hit -- and counting the steps is
-- the de Bruijn index.  So a derivation stops being mere evidence that the
-- term checks and becomes the elaborated variable: `Elaborate` reads the
-- core term off it rather than re-running the lookup.
--
-- It is still a *proposition*.  The two summands are mutually exclusive --
-- one asserts `x ≡ y`, the other refutes it -- so shadowing resolves to
-- the innermost binding and no term has two derivations.  Proof-relevant
-- and unambiguous are not in tension: the content is the position, and the
-- position is unique.
Lookup : Ctx → Ty → ℕ → Type ℓ-zero
Lookup [] A x = Empty.⊥
Lookup ((y , B) ∷ Γ) A x =
  ((x ≡ y) × (A ≡ B)) Sum.⊎ ((x ≡ y → Empty.⊥) × Lookup Γ A x)

deBruijn : (Γ : Ctx) (A : Ty) (x : ℕ) → Lookup Γ A x → ℕ
deBruijn ((y , B) ∷ Γ) A x (Sum.inl _) = 0
deBruijn ((y , B) ∷ Γ) A x (Sum.inr (_ , v)) = ℕ.suc (deBruijn Γ A x v)

private
  isPropNeq : {x y : ℕ} → isProp (x ≡ y → Empty.⊥)
  isPropNeq f g = funExt λ z → Empty.rec (f z)

isPropLookup : (Γ : Ctx) (A : Ty) (x : ℕ) → isProp (Lookup Γ A x)
isPropLookup [] A x = λ ()
isPropLookup ((y , B) ∷ Γ) A x =
  isProp⊎ (isProp× (isSetℕ _ _) (isSetTyp _ _))
          (isProp× isPropNeq (isPropLookup Γ A x))
          (λ hit miss → miss .fst (hit .fst))

Look : Ctx → Ty → TheoryTy ℓ-zero nm
Look Γ A = Lookup Γ A

LookSet : Ctx → Ty → TheorySet ℓ-zero nm
LookSet Γ A = Look Γ A , λ x → isProp→isSet (isPropLookup Γ A x)

decLook : (Γ : Ctx) (A : Ty) → Decidable (Look Γ A)
decLook [] A x _ = Sum.inr λ ()
decLook ((y , B) ∷ Γ) A x _ = onName (discreteℕ x y) (discreteTy A B)
  where
  onTail : (x ≡ y → Empty.⊥) → DecTy (Look Γ A) x
    → DecTy (Look ((y , B) ∷ Γ) A) x
  onTail ne (Sum.inl v) = Sum.inl (Sum.inr (ne , v))
  onTail ne (Sum.inr ¬v) = Sum.inr λ where
    (Sum.inl hit) → Empty.rec (ne (hit .fst))
    (Sum.inr miss) → ¬v (miss .snd)

  onName : Dec (x ≡ y) → Dec (A ≡ B) → DecTy (Look ((y , B) ∷ Γ) A) x
  onName (yes p) (yes q) = Sum.inl (Sum.inl (p , q))
  onName (yes p) (no ¬q) = Sum.inr λ where
    (Sum.inl hit) → Empty.rec (¬q (hit .snd))
    (Sum.inr miss) → Empty.rec (miss .fst p)
  onName (no ¬p) _ = onTail ¬p (decLook Γ A x tt)

-- The judgment.  Every premise's index is determined, so this is a
-- proposition: an annotated term has at most one derivation at a type, and
-- `unambiguous` is definitional rather than a theorem.
Der : Jdg → TheoryTy ℓ-zero tm
Der (Γ , A) (avar x) = Look Γ A x
Der (Γ , A) (aapp B f a) = Der (Γ , B ⇒ A) f × Der (Γ , B) a
Der (Γ , A) (alam x B t) = ArrHead A B × Der ((x , B) ∷ Γ , cod A) t

isPropDer : (i : Jdg) (t : ATm) → isProp (Der i t)
isPropDer (Γ , A) (avar x) = isPropLookup Γ A x
isPropDer (Γ , A) (aapp B f a) =
  isProp× (isPropDer (Γ , B ⇒ A) f) (isPropDer (Γ , B) a)
isPropDer (Γ , A) (alam x B t) =
  isProp× (isPropArrHead A B) (isPropDer ((x , B) ∷ Γ , cod A) t)

DerSet : Jdg → TheorySet ℓ-zero tm
DerSet i = Der i , λ t → isProp→isSet (isPropDer i t)

-- The three rules, as the slots of their nodes.
Slots : (o : AOp) → Jdg → NodeArgs ℓ-zero o
Slots varOp (Γ , A) ms theVar = LookSet Γ A
Slots (appOp B) (Γ , A) ms theFun = DerSet (Γ , B ⇒ A)
Slots (appOp B) (Γ , A) ms theArg = DerSet (Γ , B)
Slots (lamOp B) (Γ , A) ms theBinder = ArrSet A B
Slots (lamOp B) (Γ , A) ms theBody = DerSet ((ms theBinder , B) ∷ Γ , cod A)

-- One level of unfolding, both ways, as `⊢`-terms.
rollNode : (o : AOp) (i : Jdg) → ⊗ᴰ o (Slots o i) ⊢ Der i
rollNode varOp (Γ , A) m (ms , Eq.refl , ws) = ws theVar
rollNode (appOp B) (Γ , A) m (ms , Eq.refl , ws) = ws theFun , ws theArg
rollNode (lamOp B) (Γ , A) m (ms , Eq.refl , ws) = ws theBinder , ws theBody

unrollNode : (o : AOp) (i : Jdg) → Der i & NodeAt o ⊢ ⊗ᴰ o (Slots o i)
unrollNode varOp (Γ , A) m (d , (ms , Eq.refl)) =
  node-mk {ms = ms} λ where theVar → d
unrollNode (appOp B) (Γ , A) m (d , (ms , Eq.refl)) =
  node-mk {ms = ms} λ where
    theFun → d .fst
    theArg → d .snd
unrollNode (lamOp B) (Γ , A) m (d , (ms , Eq.refl)) =
  node-mk {ms = ms} λ where
    theBinder → d .fst
    theBody → d .snd


-- The checker, for whatever answer.
module Check (𝒯 : AnswerFunctor) where

  open Subterm {X = Jdg} isSetIdx (λ _ → 0) hiding (_<_) public
  open Combinators 𝒯 srt order public

  step : Step DerSet
  step (Γ , A) = look nodeCover branch
    where
    nodeAns : (o : AOp) → ▷ (AnsFam DerSet) (Γ , A) & NodeAt o
      ⊢ ty (Ans (⊗ᴰSet o (Slots o (Γ , A))))
    nodeAns varOp m (β , (ms , Eq.refl)) =
      Ans-node varOp (preciseA varOp) {As = Slots varOp (Γ , A)} {ms = ms}
        λ where theVar → Ans-ofDec (ms theVar) (decLook Γ A (ms theVar) tt)
    nodeAns (appOp B) m (β , (ms , Eq.refl)) =
      Ans-node (appOp B) (preciseA (appOp B))
        {As = Slots (appOp B) (Γ , A)} {ms = ms}
        λ where
          theFun → callAt (Γ , B ⇒ A)
            (callFun {x = Γ , A} {x' = Γ , B ⇒ A} B (ms theFun) (ms theArg)) β
          theArg → callAt (Γ , B)
            (callArg {x = Γ , A} {x' = Γ , B} B (ms theFun) (ms theArg)) β
    nodeAns (lamOp B) m (β , (ms , Eq.refl)) =
      Ans-node (lamOp B) (preciseA (lamOp B))
        {As = Slots (lamOp B) (Γ , A)} {ms = ms}
        λ where
          theBinder → Ans-ofDec (ms theBinder) (decArrHead A B (ms theBinder) tt)
          theBody → callAt ((ms theBinder , B) ∷ Γ , cod A)
            (callBody {x = Γ , A} {x' = (ms theBinder , B) ∷ Γ , cod A}
              (ms theBinder) B (ms theBody)) β

    branch : (o : AOp)
      → ▷ (AnsFam DerSet) (Γ , A) & NodeAt o ⊢ ty (Ans (DerSet (Γ , A)))
    branch o =
      Ans-map& (rollNode o (Γ , A) ∘⊢ π₁) (unrollNode o (Γ , A))
      ∘⊢ (nodeAns o ,& π₂)

  typed : Checker DerSet
  typed = fix step
