{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A type checker for the annotated lambda calculus, written once, for
   every answer -- and, since it is intrinsically typed, an elaborator.

   THE JUDGMENT CARRIES THE PROGRAM.  `Der (Γ , A) t` is not "`t` checks at
   `A`"; it is

     Σ[ c ∈ Core Γ A ] (erase c ≡ t)

   a well-typed core term together with the evidence that it is a term for
   this source.  The difference is which claims need proving.  A judgment
   defined by recursion on `t` is a definition someone wrote, and "this
   definition is STLC typing" is checked nowhere: the checker is verified
   against the judgment, the judgment against nothing.  Here `Core` IS the
   typing rules -- a constructor exists exactly when the rule applies --
   so a `yes` from the checker means a well-typed core term exists and a
   `no` means none does, both by typing, and `Elaborate`'s elaborator is
   the first projection.

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

   WHAT THE INTRINSIC FORM COSTS, honestly, is house convention 1: the
   judgment is no longer defined by recursion on the model, so `isProp` is
   no longer two lines and `unrollNode` no longer holds its premises
   already separated.  Both are paid in one place.  The old recursive
   judgment survives below as `Der⁻`, and the pair `graph`/`canon` is an
   isomorphism between it and the erasure fibre: `graph` is recursion on
   the CORE term, which hits every clause of `Der⁻` definitionally, and
   `canon` is recursion on the SOURCE, which is elaboration.  `isPropDer`
   is then a retraction onto a proposition and `unrollNode` computes the
   fibre rather than inverting `erase`.  So the extrinsic judgment is
   demoted from definition to lemma -- which is the right place for it,
   since as a definition it was the unverified layer.

   AND THE UNIFIER NEVER COMPLAINS, which was the thing to be afraid of:
   `Core` is an indexed `data`, the one shape house convention 1 warns
   against, and it is matched only against itself.  `graph`, `canon` and
   `canonUniq` each recur on one argument with the other side free, no
   clause matches a `Core` constructor against a model constructor, and the
   equations between source terms are projected rather than unified -- the
   trick `Guard` already needs for `Precise`.  So no `SplitError` arises
   anywhere below, and the only equational reasoning left is `substRefl` on
   a path in `Ty`, and `Ty` is a set.

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
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd ; Σ≡Prop)
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

-- THE CORE LANGUAGE, INTRINSICALLY TYPED.  `Core Γ A` is inhabited by
-- well-typed terms and by nothing else: `capp` may only apply a `B ⇒ A` to
-- a `B`, and `clam`'s body lives in the extended context.  No constructor
-- carries a type field for an elaborator to fill in wrongly, because the
-- type is an INDEX.
--
-- The variable constructor carries a `Lookup`, not a numeral, and that is
-- the one departure from the textbook well-scoped representation.  A
-- numeral -- a positional pointer into a type-only context -- is exactly
-- right for a nameless language and WRONG for this one: `avar 0` in the
-- context `0:ι, 0:ι` would then be the erasure of two different core
-- terms, the erasure fibre below would have two elements, and the judgment
-- would stop being a proposition.  `Lookup Γ A x` is the pointer TOGETHER
-- with the evidence that nothing nearer shadows it, which is verbatim the
-- innermost-wins rule of the surface language; `deBruijn` counts it.  So
-- the ambiguity that intrinsic syntax would introduce is refuted at the
-- constructor rather than truncated away afterwards.
data Core : Ctx → Ty → Type ℓ-zero where
  cvar : {Γ : Ctx} {A : Ty} (x : ℕ) → Lookup Γ A x → Core Γ A
  capp : {Γ : Ctx} {A B : Ty} → Core Γ (B ⇒ A) → Core Γ B → Core Γ A
  clam : {Γ : Ctx} {A B : Ty} (x : ℕ) → Core ((x , B) ∷ Γ) A → Core Γ (B ⇒ A)

-- ...and back to the surface.  `clam` keeps the binder's name and `capp`
-- reads its annotation off the TYPE INDEX, so erasure is total and
-- recovers the source exactly -- which is what makes "erases to `t`" a
-- usable premise rather than a slogan.
erase : {Γ : Ctx} {A : Ty} → Core Γ A → ATm
erase (cvar x _) = avar x
erase (capp {B = B} f a) = aapp B (erase f) (erase a)
erase (clam {B = B} x t) = alam x B (erase t)

-- Reading `A` as `B ⇒ cod A`, which is what the `lam` rule's side
-- condition says and what its core term needs.
arrEta : {B : Ty} (A : Ty) → ArrHead A B → A ≡ B ⇒ cod A
arrEta ι (h , _) = Empty.rec h
arrEta (B' ⇒ C) (_ , p) = cong (_⇒ C) p

eraseSubst : {Γ : Ctx} {A A' : Ty} (e : A ≡ A') (c : Core Γ A)
  → erase (subst (Core Γ) e c) ≡ erase c
eraseSubst {Γ = Γ} e c i = erase (subst-filler (Core Γ) e c (~ i))

-- THE JUDGMENT.  Not "`t` checks at `A`" but "here is a well-typed core
-- term, and it erases to `t`".  Elaboration is then the first projection
-- and its correctness is the type of that projection: the layer that used
-- to say "the judgment means STLC typing" -- verified nowhere, because it
-- was a claim about a definition someone wrote -- is gone, because there
-- is no longer a separate definition to compare `Core` against.
Der : Jdg → TheoryTy ℓ-zero tm
Der (Γ , A) t = Σ[ c ∈ Core Γ A ] (erase c ≡ t)

-- The judgment this file used to define, demoted from definition to
-- lemma.  It is the erasure fibre computed by recursion on the source, so
-- it is a proposition for the old two-line reason; everything below is the
-- claim that computing the fibre and taking it agree.
Der⁻ : Jdg → TheoryTy ℓ-zero tm
Der⁻ (Γ , A) (avar x) = Look Γ A x
Der⁻ (Γ , A) (aapp B f a) = Der⁻ (Γ , B ⇒ A) f × Der⁻ (Γ , B) a
Der⁻ (Γ , A) (alam x B t) = ArrHead A B × Der⁻ ((x , B) ∷ Γ , cod A) t

isPropDer⁻ : (i : Jdg) (t : ATm) → isProp (Der⁻ i t)
isPropDer⁻ (Γ , A) (avar x) = isPropLookup Γ A x
isPropDer⁻ (Γ , A) (aapp B f a) =
  isProp× (isPropDer⁻ (Γ , B ⇒ A) f) (isPropDer⁻ (Γ , B) a)
isPropDer⁻ (Γ , A) (alam x B t) =
  isProp× (isPropArrHead A B) (isPropDer⁻ ((x , B) ∷ Γ , cod A) t)

-- One direction is free: recursion on the CORE term hits each clause of
-- `Der⁻` definitionally, with no equation to transport along.  This is why
-- the fibre is computed here and inverted nowhere.
graph : {Γ : Ctx} {A : Ty} (c : Core Γ A) → Der⁻ (Γ , A) (erase c)
graph (cvar x v) = v
graph (capp f a) = graph f , graph a
graph (clam x c) = (tt , refl) , graph c

-- ...and the other is elaboration, by recursion on the SOURCE.  The `lam`
-- clause is the only place a `subst` appears in the whole development: the
-- body's core term is built at `B ⇒ cod A` and the conclusion asks for
-- `A`, and `arrEta` is the side condition rewritten as that path.
canon : (Γ : Ctx) (A : Ty) (t : ATm) → Der⁻ (Γ , A) t → Core Γ A
canon Γ A (avar x) v = cvar x v
canon Γ A (aapp B f a) d = capp (canon Γ (B ⇒ A) f (d .fst)) (canon Γ B a (d .snd))
canon Γ A (alam x B t) d = subst (Core Γ) (sym (arrEta A (d .fst)))
  (clam x (canon ((x , B) ∷ Γ) (cod A) t (d .snd)))

canonErase : (Γ : Ctx) (A : Ty) (t : ATm) (d : Der⁻ (Γ , A) t)
  → erase (canon Γ A t d) ≡ t
canonErase Γ A (avar x) v = refl
canonErase Γ A (aapp B f a) d =
  cong₂ (aapp B) (canonErase Γ (B ⇒ A) f (d .fst)) (canonErase Γ B a (d .snd))
canonErase Γ A (alam x B t) d =
    eraseSubst (sym (arrEta A (d .fst))) (clam x (canon ((x , B) ∷ Γ) (cod A) t (d .snd)))
  ∙ cong (alam x B) (canonErase ((x , B) ∷ Γ) (cod A) t (d .snd))

-- Elaborating a term that came from a core term returns that core term.
-- By induction on the CORE term, so the `lam` case is a `subst` along a
-- path in `Ty` that is already `refl`, rather than an inversion of
-- erasure.  This is the entire content of unambiguity.
canonUniq : {Γ : Ctx} {A : Ty} (c : Core Γ A) → canon Γ A (erase c) (graph c) ≡ c
canonUniq (cvar x v) = refl
canonUniq (capp f a) = cong₂ capp (canonUniq f) (canonUniq a)
canonUniq (clam {Γ = Γ} x c) =
  substRefl {B = Core Γ} (clam x (canon _ _ (erase c) (graph c)))
  ∙ cong (clam x) (canonUniq c)

into : (i : Jdg) → Der i ⊢ Der⁻ i
into (Γ , A) t d = subst (Der⁻ (Γ , A)) (d .snd) (graph (d .fst))

from : (i : Jdg) → Der⁻ i ⊢ Der i
from (Γ , A) t d = canon Γ A t d , canonErase Γ A t d

fromInto : (i : Jdg) (t : ATm) (d : Der i t) → from i t (into i t d) ≡ d
fromInto (Γ , A) t (c , p) = Σ≡Prop (λ c' → isSetCrr tm (erase c') t) (onEq t p)
  where
  onEq : (t' : ATm) (q : erase c ≡ t')
    → canon Γ A t' (subst (Der⁻ (Γ , A)) q (graph c)) ≡ c
  onEq t' q =
    J (λ t'' q' → canon Γ A t'' (subst (Der⁻ (Γ , A)) q' (graph c)) ≡ c)
      (cong (canon Γ A (erase c)) (substRefl {B = Der⁻ (Γ , A)} (graph c))
        ∙ canonUniq c) q

-- ...so the intrinsic judgment is a proposition after all, and it is one
-- for a reason worth naming: the surface language is unambiguous, and
-- `Der` is a retract of the computed fibre rather than a truncation of it.
isPropDer : (i : Jdg) (t : ATm) → isProp (Der i t)
isPropDer i t =
  isOfHLevelRetract 1 (into i t) (from i t) (fromInto i t) (isPropDer⁻ i t)

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
--
-- ROLL CONSTRUCTS CORE SYNTAX.  It is not the data shuffle it was: each
-- clause applies the core constructor for its operation and pairs it with
-- the erasure equation assembled from the slots'.  So the core term the
-- checker returns is built by the checker, one node at a time, and `elab`
-- is a projection out of it rather than a second pass that could disagree.
rollNode : (o : AOp) (i : Jdg) → ⊗ᴰ o (Slots o i) ⊢ Der i
rollNode varOp (Γ , A) m (ms , Eq.refl , ws) = cvar (ms theVar) (ws theVar) , refl
rollNode (appOp B) (Γ , A) m (ms , Eq.refl , ws) =
    capp (ws theFun .fst) (ws theArg .fst)
  , cong₂ (aapp B) (ws theFun .snd) (ws theArg .snd)
rollNode (lamOp B) (Γ , A) m (ms , Eq.refl , ws) =
    subst (Core Γ) (sym (arrEta A (ws theBinder)))
      (clam (ms theBinder) (ws theBody .fst))
  , eraseSubst (sym (arrEta A (ws theBinder)))
      (clam (ms theBinder) (ws theBody .fst))
  ∙ cong (alam (ms theBinder) B) (ws theBody .snd)

-- UNROLL GOES THROUGH THE FIBRE.  It computes the fibre with `into`,
-- splits it -- definitionally, since `Der⁻` is recursion on the source --
-- and re-elaborates each slot with `from`.
--
-- The alternative is to invert `erase` directly: match on the conclusion's
-- core term, refute the two wrong heads with a discriminator, and project
-- the equation with `Guard`'s `appFun`/`lamBd`.  That is writable -- it was
-- written, and it typechecks -- at a cost of one `subst` per index the
-- constructor binds, three for `lam`, each with its own `subst-filler`
-- lemma to move `erase` across.  It buys nothing here: `Der` is a
-- proposition, so the two unrollings are equal, and `canon` has to exist
-- anyway for `isPropDer`.  The general shape of the trade is that an
-- intrinsic judgment pays for inversion once, either in transports or in a
-- computed fibre, and the computed fibre is the same work the propositional
-- reasoning needs.
--
-- Either way the round trip is never run on the accepting path, since
-- `Ans-map&`'s backward map exists only to carry a refutation.
unrollNode : (o : AOp) (i : Jdg) → Der i & NodeAt o ⊢ ⊗ᴰ o (Slots o i)
unrollNode varOp (Γ , A) m (d , (ms , Eq.refl)) =
  node-mk {ms = ms} λ where theVar → into (Γ , A) _ d
unrollNode (appOp B) (Γ , A) m (d , (ms , Eq.refl)) =
  node-mk {ms = ms} λ where
    theFun → from (Γ , B ⇒ A) (ms theFun) (into (Γ , A) _ d .fst)
    theArg → from (Γ , B) (ms theArg) (into (Γ , A) _ d .snd)
unrollNode (lamOp B) (Γ , A) m (d , (ms , Eq.refl)) =
  node-mk {ms = ms} λ where
    theBinder → into (Γ , A) _ d .fst
    theBody → from ((ms theBinder , B) ∷ Γ , cod A) (ms theBody)
      (into (Γ , A) _ d .snd)

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
