{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- TYPE INFERENCE FOR UNANNOTATED TERMS, AS TWO CLIENTS JOINED AT A SIDE
   CONDITION.

   This is the first judgment in the development whose premises are
   discharged by ANOTHER client of the framework.  The claim to test was:
   `Unify/Check` runs at the decidable answer and so exports a `Decidable`;
   `Core`'s `side` takes exactly a `Decidable`; therefore solving a
   constraint should enter an inference rule the way `decLook` does.  It
   does, and `decSolv` below is the whole of the join -- four tokens of
   plumbing, no change to `Core`, no change to `Unify`.

   WHAT THE JOIN COST, EXACTLY.  Three things, and they are the report.

   1.  THE INNER CLIENT IS PINNED TO `Dec`.  `Ans-ofDec` consumes a
       DECISION, so the sub-checker must have been run at
       `Answer/Decidable` before the outer answer is chosen.  The outer
       client is still polymorphic -- `Check 𝒯` below takes any
       `AnswerFunctor`, and all three are instantiated in `Elaborate` --
       but the composite is not: an inference checker at `ND` still calls a
       unifier at `Dec`.  The side-condition mechanism is a one-way door,
       and nothing in `Core` offers the other direction (an `Ans A ⊢ Ans B`
       taking an answer for granted would be a bind, which is exactly what
       `Ans-re`'s comment says the framework declines to provide).

   2.  UNIFICATION IS GLOBAL, AND A SIDE CONDITION IS LOCAL, SO THE JOIN
       HAPPENS AT A MODE CHANGE AND NOT AT EVERY RULE.  Threading a
       substitution through sibling premises is a premise index that is a
       previous premise's OUTPUT, which no combinator provides; and the
       obvious repair -- solve at every node -- is degenerate, since the
       node's constraint set CONTAINS its children's, so the premises would
       carry no information the side condition did not already have.  What
       is left is the honest factorisation: a syntax-directed judgment that
       postpones every equation between types (`Base`'s `Gen`, `gen`), and
       ONE conjunction with `Sol`.  `Bidir`'s two-mode family is the shape
       that fits -- `infM i` calls `genM i` at the same term on the guard's
       rank, and conjoins the decision with `Ans-&&` -- so the mechanism
       used is house-standard even though the theorem it composes is new.

   3.  `Gen` IS THIN, AND IT HAS TO BE.  Once every type equation is
       postponed, what remains of typing over the term theory is which
       names are bound and where the fresh unknowns go.  So the interesting
       reading of this client is not "the judgment got stronger" but "the
       judgment SPLIT": `Gen` is the part of inference that is
       syntax-directed, `Sol` is the part that is not, and the split is
       forced rather than chosen.  The content that was lost from the
       judgment is recovered as a CARRIED OBJECT instead -- `Elaborate`'s
       `verified` turns a derivation at `infM` into an intrinsically typed
       `Core` term with its erasure equation, which is `Annotated`'s
       discipline reached by a theorem rather than by a definition.

   WHAT `no` MEANS.  Not "this term has no type".  The two conjuncts refuse
   for different reasons and only one of the refusals is complete, so they
   are stated apart.

     `no` at `genM i`  =  NO WELL-TYPED CORE TERM ERASES TO THIS TERM, AT
                          ANY TYPES WHATEVER.  This is genuine, and it is
                          proved: `Base`'s `genComplete` takes a `Core` at
                          an arbitrary scope of unknowns, an arbitrary
                          context agreeing with this one in its NAMES, and
                          an arbitrary type, and produces the `Gen`
                          derivation.  The universal over infinitely many
                          types is discharged rather than dodged, and the
                          reason it can be is that `Gen` quantifies over no
                          types at all -- it reads only which names are
                          bound.  So the shape half of inference has the
                          completeness `Bidir` and `Annotated` had, and has
                          it for the same reason: nothing is being guessed.

     `no` at `infM i`  =  either the above, or the machine `Unify`'s `Sol`
                          describes does not run to completion on the
                          generated stack.  THIS IS NOT COMPLETENESS, and
                          the gap is not one this client introduces:
                          `Unify/Correct` proves `Sol → Unifier` and its
                          closing comment says precisely why the converse
                          is not available -- `Ans-map&`'s backward map
                          would have to restrict an `AList (suc n)` to an
                          `AList n`, and an `AList` is a CHAIN of
                          scope-dropping assignments, which restriction
                          does not preserve.  So a refusal here means "the
                          composite machine failed", and every step from
                          there to "this term is untypable" is unproved.

   THREE STEPS ARE MISSING, and naming them is the point of the paragraph.
   (i) that a term with a solvable constraint set has a `Sol` derivation --
   McBride's algorithm is complete in the literature, but nothing in this
   development says so; (ii) that `gen` is complete, i.e. that a typing
   derivation for `t` yields a substitution solving `gen`, which is `sound`
   run backwards and would need `mvar` to be injective -- true, and
   unformalised, see `Base`; (iii) that a most general solution exists,
   which is (i) again.  None of the three is hard in the sense of being
   open; all three are absent, and the composite's `no` is exactly as
   strong as the weakest of them, which is to say: it is the machine's
   verdict and not the specification's.

   Worth stating generally, since it is the structural fact and not an
   accident of effort.  A judgment refuted NODE BY NODE -- `Annotated`,
   `Bidir`, `Gen` above -- gets completeness from the cover's `total`, free.
   A judgment whose refutation is an existential over SUBSTITUTIONS gets
   nothing from the cover, because no cover of the term model splits by
   solvability.  The framework's `Ans-map&` is what would force the issue,
   and this client answers it by putting the existential in a side
   condition, where `Ans-ofDec` asks for a decision and not for a
   characterisation.  That is the honest boundary, and it is the same
   boundary `Unify` reached from the other side.

   Nothing below mentions `Dec`, `Maybe` or `ND` for its OWN answer.
   `decSolv` mentions the decidable answer of the OTHER client, and that
   mention is the join. -}
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

-- The trivially true condition on a bound name, and the trivially true
-- decision that lets it enter through `Ans-ofDec` like every other slot.
-- `Lambda/Scope` names both for the same reason: an exception to house
-- convention 5 costs more than a line.
⊤Set : {s : LSort} → TheorySet ℓ-zero s
⊤Set = ⊤Ty , isSet⊤Ty

dec⊤ : {s : LSort} → Decidable (⊤Ty {s = s})
dec⊤ _ _ = Sum.inl tt


-- The `var` rule's premise.  The TYPE is not an index here, as it is in
-- `Annotated`: it is READ OFF the context by `lookD`, and the equation
-- against the goal type is what `gen` postponed.  So the decided premise
-- says only that the name is bound -- `lookDef` is the proof that this is
-- no weaker than asking at the right type.
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


-- The index of the family: a scope of unknowns, a context and a goal type
-- over it, and the offset the next fresh unknown is taken from.  The
-- offset is `nx` and not `k` throughout, because `Code/Base`'s `k` -- a
-- `Functor` constructor -- is in scope through the framework's public
-- re-exports, and a pattern variable that shadows a constructor is a
-- pattern match on it.
Goal : Type ℓ-zero
Goal = Σ[ n ∈ ℕ ] (Ctx n × Tm n × ℕ)

isSetGoal : isSet Goal
isSetGoal = isSetΣ isSetℕ λ _ → isSet× isSetCtx (isSet× isSetTm isSetℕ)

GenSet : Goal → TheorySet ℓ-zero tm
GenSet (n , Γ , A , nx) =
  (λ t → Gen n Γ A nx t) , λ t → isProp→isSet (isPropGen n Γ A nx t)

-- THE SIDE CONDITION THAT IS ANOTHER CLIENT.  `Solv i t` is a closed
-- proposition about a stack of equations -- `Unify`'s judgment at the term
-- theory's model element -- and `decSolv` is its decision, which is
-- `Unify`'s own checker at the decidable answer, applied.
Solv : Goal → TheoryTy ℓ-zero tm
Solv (n , Γ , A , nx) t = Sol n (gen n Γ A nx t)

SolvSet : Goal → TheorySet ℓ-zero tm
SolvSet (n , Γ , A , nx) =
  (λ t → Sol n (gen n Γ A nx t)) , λ t → isSetSol n (gen n Γ A nx t)

decSolv : (i : Goal) → Decidable (Solv i)
decSolv (n , Γ , A , nx) t _ = U.CD.unify n (gen n Γ A nx t) tt

-- ...and the judgment that is the two of them.  `&Set` on the nose, so
-- that `Ans-&&` produces this and not something isomorphic to it.
InfSet : Goal → TheorySet ℓ-zero tm
InfSet i = GenSet i &Set SolvSet i


-- The two modes.  `infM` is the larger, because it is DEFINED as `genM`
-- conjoined with a decision at the very same term -- the same forcing
-- `Bidir`'s header describes, with `&` in place of `⊕ᴰ`.
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

-- THE MODE CHANGE, in the order `Lambda/Guard` already provides.  That
-- module's `Subterm` names only the subterm calls, because no client of it
-- had two modes at one term; the step is nonetheless the second component
-- of `ilexOrder`'s pair dropping while the first stands still, and it is
-- spelled here rather than added there so that nothing already checked
-- moves.
open Subterm {X = Mode} isSetMode rankM using (_<_)

modeStep : {x x' : Mode} {t : RawTm} → rankM x' NO.< rankM x → (x' , t) < (x , t)
modeStep lt = lift (Sum.inr (refl , lt))


-- The three rules, as the slots of their nodes.  Read as premises and
-- nothing else, per house convention 3: the fresh unknowns and the offsets
-- are index arithmetic, and every one of them is a function of this node's
-- index and of a slot's VALUE -- `mv (ms theFun)` reads slot zero, and
-- `ms theBinder` IS slot zero.
Slots : (o : LOp) → Goal → NodeArgs ℓ-zero o
Slots varOp (n , Γ , A , nx) ms theVar = LookDSet Γ
Slots appOp (n , Γ , A , nx) ms theFun = GenSet (n , Γ , mvar n nx ⇛ A , suc nx)
Slots appOp (n , Γ , A , nx) ms theArg =
  GenSet (n , Γ , mvar n nx , suc (nx + mv (ms theFun)))
Slots lamOp (n , Γ , A , nx) ms theBinder = ⊤Set
Slots lamOp (n , Γ , A , nx) ms theBody =
  GenSet (n , (ms theBinder , mvar n nx) ∷ Γ , mvar n (suc nx) , suc (suc nx))

-- One level of unfolding, both ways, as `⊢`-terms.  `Gen` is a recursion
-- on the model, so both directions are the identity once the cover cell
-- has said which node this is -- house convention 1 earning its keep.
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


-- The checker, for whatever answer.
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

  -- THE MODE CHANGE, AND THE JOIN.  Same term, smaller rank, and the
  -- decision of the other client conjoined at the node with `Ans-&&`.
  -- This is the only rule in the development whose premise is a checker
  -- over a different theory.
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
