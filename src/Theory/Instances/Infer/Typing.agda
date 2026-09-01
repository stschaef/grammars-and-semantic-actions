{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Type inference: `Gen` (syntax-directed) conjoined with `Sol` (discharged by `Unify`'s checker).
   Known gap: completeness of `gen` — the one place `mvar`'s injectivity would be load-bearing
   (a collision STRENGTHENS the constraint set: cannot cost soundness, can cost completeness). -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary hiding (Tm)
open SortedSig
open SortedEqns
module Theory.Instances.Infer.Typing where

open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; isSetℕ ; discreteℕ)
import Cubical.Data.Nat.Order as NO
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no)
import Cubical.Data.Sum as Sum
open import Cubical.Data.Sum using (isSet⊎)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Infer.Base public
open import Theory.Instances.Lambda.Guard ℕ isSetℕ public
  hiding (RawTm ; tvar ; tapp ; tlam)

import Theory.Instances.Unify.Check as U

private variable n : ℕ

⊤Set : {s : LSort} → TheorySet ℓ-zero s
⊤Set = ⊤Ty , isSet⊤Ty

dec⊤ : {s : LSort} → Decidable (⊤Ty {s = s})
dec⊤ _ _ = Sum.inl tt


-- Unlike `Annotated`, the type is READ OFF the context by `lookD`; the equation
-- against the goal is what `gen` postponed (`lookDef`: this is no weaker).
Look : Ctx n → Tm n → TheoryTy ℓ-zero nm
Look Γ A = Lookup Γ A

decLook : (Γ : Ctx n) (A : Tm n) → Decidable (Look Γ A)
decLook [] A x _ = Sum.inr λ ()
decLook ((y , B) ∷ Γ) A x _ = onName (discreteℕ x y) (discreteTm A B)
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

LookD : Ctx n → TheoryTy ℓ-zero nm
LookD Γ x = Lookup Γ (lookD Γ x) x

LookDSet : Ctx n → TheorySet ℓ-zero nm
LookDSet Γ = LookD Γ , λ x → isProp→isSet (isPropLookup Γ (lookD Γ x) x)

decLookD : (Γ : Ctx n) → Decidable (LookD Γ)
decLookD Γ x u = decLook Γ (lookD Γ x) x u


-- Offset is `nx`, not `k`: `Code/Base`'s `k` is a `Functor` constructor in scope,
-- and a pattern variable that shadows a constructor is a match on it.
Goal : Type ℓ-zero
Goal = Σ[ n ∈ ℕ ] (Ctx n × Tm n × ℕ)

isSetGoal : isSet Goal
isSetGoal = isSetΣ isSetℕ λ _ → isSet× isSetCtx (isSet× isSetTm isSetℕ)

GenSet : Goal → TheorySet ℓ-zero tm
GenSet (n , Γ , A , nx) =
  (λ t → Gen n Γ A nx t) , λ t → isProp→isSet (isPropGen n Γ A nx t)

Solv : Goal → TheoryTy ℓ-zero tm
Solv (n , Γ , A , nx) t = Sol n (gen n Γ A nx t)

SolvSet : Goal → TheorySet ℓ-zero tm
SolvSet (n , Γ , A , nx) =
  (λ t → Sol n (gen n Γ A nx t)) , λ t → isSetSol n (gen n Γ A nx t)

decSolv : (i : Goal) → Decidable (Solv i)
decSolv (n , Γ , A , nx) t _ = U.CD.unify n (gen n Γ A nx t) tt

-- `&Set` on the nose, so `Ans-&&` produces this and not something isomorphic to it.
InfSet : Goal → TheorySet ℓ-zero tm
InfSet i = GenSet i &Set SolvSet i

-- Contraposing `genCell` turns the checker's refusal into a statement about core terms;
-- see `Base` for why the reading with `¬ Cor` as a cell does not exist.
CorTy : (i : Goal) → TheoryTy ℓ-zero tm
CorTy (n , Γ , A , nx) = Cor Γ

genInto : (i : Goal) → CorTy i ⊢ ty (GenSet i)
genInto (n , Γ , A , nx) t z = genCell n Γ A nx t z

refuteCor : (i : Goal) → ¬Ty (ty (GenSet i)) ⊢ ¬Ty (CorTy i)
refuteCor i = ¬Ty-map (genInto i)

GenOrNoCor : (i : Goal) → TheoryTy ℓ-zero tm
GenOrNoCor i = ty (GenSet i) ⊕ ¬Ty (CorTy i)

genVerdict : (i : Goal) → DecTy (ty (GenSet i)) ⊢ GenOrNoCor i
genVerdict i = ⊕-elim inl (inr ∘⊢ refuteCor i)


Mode : Type ℓ-zero
Mode = Goal Sum.⊎ Goal

pattern genM i = Sum.inl i
pattern infM i = Sum.inr i

isSetMode : isSet Mode
isSetMode = isSet⊎ isSetGoal isSetGoal

rankM : Mode → ℕ
rankM (genM _) = 0
rankM (infM _) = 1

Jdg : Mode → TheorySet ℓ-zero tm
Jdg (genM i) = GenSet i
Jdg (infM i) = InfSet i

-- Mode step: `ilexOrder`'s second component drops while the first stands still.
open Subterm {X = Mode} isSetMode rankM using (_<_)

modeStep : {x x' : Mode} {t : RawTm} → rankM x' NO.< rankM x → (x' , t) < (x , t)
modeStep lt = lift (Sum.inr (refl , lt))


-- Fresh unknowns/offsets are functions of the node's index and slot VALUES
-- (`mv (ms theFun)` reads slot zero; `ms theBinder` IS slot zero).
Slots : (o : LOp) → Goal → NodeArgs ℓ-zero o
Slots varOp (n , Γ , A , nx) ms theVar = LookDSet Γ
Slots appOp (n , Γ , A , nx) ms theFun = GenSet (n , Γ , mvar n nx ⇛ A , suc nx)
Slots appOp (n , Γ , A , nx) ms theArg =
  GenSet (n , Γ , mvar n nx , suc (nx + mv (ms theFun)))
Slots lamOp (n , Γ , A , nx) ms theBinder = ⊤Set
Slots lamOp (n , Γ , A , nx) ms theBody =
  GenSet (n , (ms theBinder , mvar n nx) ∷ Γ , mvar n (suc nx) , suc (suc nx))

-- Both directions are the identity once the cover cell has said which node this is.
rollNode : (o : LOp) (i : Goal) → ⊗ᴰ o (Slots o i) ⊢ ty (GenSet i)
rollNode varOp i m (ms , Eq.refl , ws) = ws theVar
rollNode appOp i m (ms , Eq.refl , ws) = ws theFun , ws theArg
rollNode lamOp i m (ms , Eq.refl , ws) = ws theBody

unrollNode : (o : LOp) (i : Goal) → ty (GenSet i) & NodeAt o ⊢ ⊗ᴰ o (Slots o i)
unrollNode varOp i m (d , (ms , Eq.refl)) =
  node-mk {ms = ms} λ where theVar → d
unrollNode appOp i m (d , (ms , Eq.refl)) =
  node-mk {ms = ms} λ where
    theFun → d .fst
    theArg → d .snd
unrollNode lamOp i m (d , (ms , Eq.refl)) =
  node-mk {ms = ms} λ where
    theBinder → tt
    theBody → d


module Check (𝒯 : AnswerFunctor) where

  open Subterm {X = Mode} isSetMode rankM hiding (_<_) public
  open Combinators 𝒯 srt order public

  nodeAns : (i : Goal) (o : LOp)
    → ▷ (AnsFam Jdg) (genM i) & NodeAt o ⊢ ty (Ans (⊗ᴰSet o (Slots o i)))
  nodeAns (n , Γ , A , nx) varOp m (β , (ms , Eq.refl)) =
    Ans-node varOp (preciseλ varOp) {As = Slots varOp (n , Γ , A , nx)} {ms = ms}
      λ where theVar → Ans-ofDec (ms theVar) (decLookD Γ (ms theVar) tt)
  nodeAns (n , Γ , A , nx) appOp m (β , (ms , Eq.refl)) =
    Ans-node appOp (preciseλ appOp) {As = Slots appOp (n , Γ , A , nx)} {ms = ms}
      λ where
        theFun → callAt (genM (n , Γ , mvar n nx ⇛ A , suc nx))
          (callFun {x = genM (n , Γ , A , nx)}
                   {x' = genM (n , Γ , mvar n nx ⇛ A , suc nx)}
                   (ms theFun) (ms theArg)) β
        theArg → callAt (genM (n , Γ , mvar n nx , suc (nx + mv (ms theFun))))
          (callArg {x = genM (n , Γ , A , nx)}
                   {x' = genM (n , Γ , mvar n nx , suc (nx + mv (ms theFun)))}
                   (ms theFun) (ms theArg)) β
  nodeAns (n , Γ , A , nx) lamOp m (β , (ms , Eq.refl)) =
    Ans-node lamOp (preciseλ lamOp) {As = Slots lamOp (n , Γ , A , nx)} {ms = ms}
      λ where
        theBinder → Ans-ofDec (ms theBinder) (dec⊤ (ms theBinder) tt)
        theBody → callAt (genM (n , (ms theBinder , mvar n nx) ∷ Γ
                              , mvar n (suc nx) , suc (suc nx)))
          (callBody {x = genM (n , Γ , A , nx)}
                    {x' = genM (n , (ms theBinder , mvar n nx) ∷ Γ
                              , mvar n (suc nx) , suc (suc nx))}
                    (ms theBinder) (ms theBody)) β

  genBranch : (i : Goal) (o : LOp)
    → ▷ (AnsFam Jdg) (genM i) & NodeAt o ⊢ ty (Ans (GenSet i))
  genBranch i o =
    Ans-map& (rollNode o i ∘⊢ π₁) (unrollNode o i) ∘⊢ (nodeAns i o ,& π₂)

  infStep : (i : Goal) → ▷ (AnsFam Jdg) (infM i) ⊢ ty (Ans (InfSet i))
  infStep i = Ans-&& ∘⊢ (shape ,& side (decSolv i))
    where
    shape : ▷ (AnsFam Jdg) (infM i) ⊢ ty (Ans (GenSet i))
    shape t β = callAt (genM i)
      (modeStep {x = infM i} {x' = genM i} {t = t} (0 , refl)) β

  step : Step Jdg
  step (genM i) = look nodeCover (genBranch i)
  step (infM i) = infStep i

  inferred : Checker Jdg
  inferred = fix step
