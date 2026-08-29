{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Typeclass instance resolution, and the identification the framework was
   missing a field for:

     `Route`'s `disjoint`, for instance resolution, IS COHERENCE.

   `Resolve C τ` -- "class `C` has an instance at type `τ`" -- is
   syntax-directed on `τ`, and every premise's index is determined: the
   instance `Eq a => Eq (List a)` fires at `List a` and its one premise sits
   at `a`, a proper subtype.  So the node, the guard and the slots are the
   ordinary `Combinator/Core` story.

   What is *not* determined is WHICH INSTANCE.  A judgment is

       Resolve C τ  =  ⊕[ i ∈ Inst C ] (instance `i` applies at τ)

   -- an indexed sum, and answering an indexed sum is precisely what
   `AnswerFunctor` could not do before `Ans-route`.  The `Route` supplies a
   `Cover` of the type language by `Maybe (Inst C)`: the cell of `just i` is
   "τ's head constructor is instance `i`'s head", the cell of `nothing` is
   "no instance's head matches".  Then

     * `total`    = resolution terminates: some instance's head matches, or
                    provably none does.  It is the finite search over the
                    table, and it is where a *decidable* table is used.
     * `disjoint` = COHERENCE: no two distinct instances of a class match
                    the same type.  Spelled out, `disjoint (just i) (just j)`
                    for `i ≠ j` asks for `NodeAt (head i) & NodeAt (head j)
                    ⊢ ⊥Ty`, and the only way to get it is to know the heads
                    differ -- which is the `Coherent` condition below,
                    verbatim.
     * `into`     = an instance that applies does match its own head.

   That is not an analogy.  `Coherent T` is the exact hypothesis
   `Routed.route` needs and the exact thing GHC's coherence check verifies.

   The other half.  An *incoherent* table has no `Route`, so it has no
   routed resolver -- statically, not as a runtime failure.  What it does
   have is `Ans-anyFin`, which asks every instance and keeps every answer:
   available to `Maybe` and `ND`, never to `Dec`, because enumeration needs
   an empty answer and a decision cannot decline.  So the two `Pick`s below
   are the whole design tension in two lines: `routed` demands coherence and
   commits; `ambig` demands nothing and counts.  At `ND` the count is the
   number of instances that fired, and a count above one is the incoherence,
   exhibited.  `Instances/Class/ResolveTests` does exactly that.

   Proof-relevance.  A derivation of `Resolve C τ` is a tree of instance
   choices -- which is to say it is the DICTIONARY.  `dictOf` folds it,
   `dictAction` makes that a `SemanticAction`, and `resolve` is
   `observe checker (semact-dec dictAction)`, the same three-term
   composition as `Annotated/Elaborate`'s `compile`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Cubical.Data.Equality as Eq
module Theory.Instances.Class.Resolve where

open import Cubical.Data.Empty using (⊥)
import Cubical.Data.Empty as Empty
open import Cubical.Data.FinData using (Fin ; zero ; suc ; toℕ)
open import Cubical.Data.FinData.Properties using (isSetFin)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt ; isPropUnit)
import Cubical.Data.Sum as Sum
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no ; Discrete)
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)

open import Theory.Instances.Class.Base public
open import Theory.Type.SemanticAction.Base CEqns ⊥ (λ ()) cPresentation
import Theory.Combinator.Answer.Decidable CEqns ⊥ (λ ()) cPresentation as D

-- The dictionary: which instance was chosen, and the dictionaries its
-- context demanded.  A `Dict` is the derivation with the proofs erased and
-- the choices kept -- which is all a compiler wants from it.
data Dict : Type ℓ-zero where
  dict : ℕ → List Dict → Dict

-- Class names.  The index `X` of the mutually recursive family: one
-- component of the resolver per class.
data Cls : Type ℓ-zero where
  eqC ordC : Cls

private
  IsEq IsOrd : Cls → Type ℓ-zero
  IsEq eqC = Unit
  IsEq ordC = ⊥
  IsOrd eqC = ⊥
  IsOrd ordC = Unit

discreteCls : Discrete Cls
discreteCls eqC eqC = yes refl
discreteCls eqC ordC = no λ p → subst IsEq p tt
discreteCls ordC eqC = no λ p → subst IsOrd p tt
discreteCls ordC ordC = yes refl

isSetCls : isSet Cls
isSetCls = Discrete→isSet discreteCls

-- Deciding an instance name in `Eq`, so that `routeIn`'s matching refines.
decFinEq : {n : ℕ} → DiscreteEq (Fin n)
decFinEq zero zero = Sum.inl Eq.refl
decFinEq zero (suc j) = Sum.inr λ ()
decFinEq (suc i) zero = Sum.inr λ ()
decFinEq (suc i) (suc j) = onPred (decFinEq i j)
  where
  onPred : (i Eq.≡ j) Sum.⊎ ((i Eq.≡ j) → ⊥)
    → (suc i Eq.≡ suc j) Sum.⊎ ((suc i Eq.≡ suc j) → ⊥)
  onPred (Sum.inl Eq.refl) = Sum.inl Eq.refl
  onPred (Sum.inr ne) = Sum.inr λ where Eq.refl → ne Eq.refl

-- The finite search the route's `total` performs.  `Inst C` is `Fin n`, so
-- a table is searchable by head for free; an infinite table would have to
-- supply this, and that is the honest content of "the table is closed".
findFin : {ℓp : Level} {n : ℕ} {P : Fin n → Type ℓp}
  → ((i : Fin n) → P i Sum.⊎ (P i → ⊥))
  → (Σ[ i ∈ Fin n ] P i) Sum.⊎ ((i : Fin n) → P i → ⊥)
findFin {n = zero} d = Sum.inr λ ()
findFin {n = suc n} {P = P} d = onHead (d zero)
  where
  onTail : (P zero → ⊥)
    → (Σ[ i ∈ Fin n ] P (suc i)) Sum.⊎ ((i : Fin n) → P (suc i) → ⊥)
    → (Σ[ i ∈ Fin (suc n) ] P i) Sum.⊎ ((i : Fin (suc n)) → P i → ⊥)
  onTail n0 (Sum.inl (i , p)) = Sum.inl (suc i , p)
  onTail n0 (Sum.inr miss) = Sum.inr λ where
    zero → n0
    (suc i) → miss i

  onHead : P zero Sum.⊎ (P zero → ⊥)
    → (Σ[ i ∈ Fin (suc n) ] P i) Sum.⊎ ((i : Fin (suc n)) → P i → ⊥)
  onHead (Sum.inl p) = Sum.inl (zero , p)
  onHead (Sum.inr n0) = onTail n0 (findFin λ i → d (suc i))

-- THE TABLE.  An instance is: a head constructor, and a class demanded of
-- each argument of that head.  `Eq a => Eq (List a)` is `head = lstOp`,
-- `ctx theElem = eqC`; `Eq ι` is `head = ιOp` and an empty context.
--
-- Nothing here mentions a *type* -- an instance head is a constructor, not
-- a pattern.  That restriction is what makes resolution syntax-directed at
-- all, and it is the restriction Haskell's `instance` heads obey up to
-- arity.  A two-level head (`instance Eq (List ι)`) would need patterns and
-- is exactly the shape that makes overlap possible; see the header.
record Table : Type ℓ-zero where
  field
    size : Cls → ℕ
    head : (C : Cls) → Fin (size C) → COp
    ctx  : (C : Cls) (i : Fin (size C)) → arities CSig (head C i) → Cls

-- COHERENCE, as a condition on the table: no two instances of one class
-- share a head.  This is `Route`'s `disjoint` in the only form the type
-- language permits, and `Routed.route` below needs it and nothing else.
Coherent : Table → Type ℓ-zero
Coherent T = (C : Cls) (i j : Fin (T .Table.size C))
  → T .Table.head C i Eq.≡ T .Table.head C j → i Eq.≡ j


module Resolver (T : Table) where
  open Table T

  Inst : Cls → Type ℓ-zero
  Inst C = Fin (size C)

  -- The judgment, by mutual recursion on the type.  Not an indexed `data`:
  -- a family indexed by `Typ` would make every branch of the resolver a
  -- `SplitError.UnificationStuck`, and `Annotated/Typing`'s `Der` avoids it
  -- the same way.
  --
  -- `Match o P τ` is the body of an instance with head `o` and context `P`:
  -- `τ` must have head `o`, and each argument must resolve at the class `P`
  -- names there.  Off the head it is `⊥` -- an instance simply does not
  -- fire.
  ResTy : Cls → Typ → Type ℓ-zero
  MatchTy : (o : COp) (P : arities CSig o → Cls) → Typ → Type ℓ-zero

  ResTy C t = Σ[ i ∈ Inst C ] MatchTy (head C i) (ctx C i) t

  MatchTy ιOp   P ι       = Unit
  MatchTy ιOp   P (lst _) = ⊥
  MatchTy ιOp   P (_ ⇒ _) = ⊥
  MatchTy lstOp P ι       = ⊥
  MatchTy lstOp P (lst a) = ResTy (P theElem) a
  MatchTy lstOp P (_ ⇒ _) = ⊥
  MatchTy arrOp P ι       = ⊥
  MatchTy arrOp P (lst _) = ⊥
  MatchTy arrOp P (a ⇒ b) = ResTy (P theDom) a × ResTy (P theCod) b

  isSetResTy : (C : Cls) → isSetTheoryTy (ResTy C)
  isSetMatchTy : (o : COp) (P : arities CSig o → Cls)
    → isSetTheoryTy (MatchTy o P)

  isSetResTy C t =
    isSetΣ isSetFin λ i → isSetMatchTy (head C i) (ctx C i) t

  isSetMatchTy ιOp   P ι       = isProp→isSet isPropUnit
  isSetMatchTy ιOp   P (lst _) = isProp→isSet (λ ())
  isSetMatchTy ιOp   P (_ ⇒ _) = isProp→isSet (λ ())
  isSetMatchTy lstOp P ι       = isProp→isSet (λ ())
  isSetMatchTy lstOp P (lst a) = isSetResTy (P theElem) a
  isSetMatchTy lstOp P (_ ⇒ _) = isProp→isSet (λ ())
  isSetMatchTy arrOp P ι       = isProp→isSet (λ ())
  isSetMatchTy arrOp P (lst _) = isProp→isSet (λ ())
  isSetMatchTy arrOp P (a ⇒ b) =
    isSet× (isSetResTy (P theDom) a) (isSetResTy (P theCod) b)

  MatchSet : (o : COp) (P : arities CSig o → Cls) → TheorySet ℓ-zero tyS
  MatchSet o P = MatchTy o P , isSetMatchTy o P

  -- The alternatives of the sum: one grammar per instance of the class.
  Alt : (C : Cls) → Inst C → TheorySet ℓ-zero tyS
  Alt C i = MatchSet (head C i) (ctx C i)

  -- ...and the judgment as that sum, on the nose.  `Ans-route` produces an
  -- answer at `⊕ᴰSet sY Φ`, so this has to *be* that and not merely be
  -- isomorphic to it.
  ResSet : Cls → TheorySet ℓ-zero tyS
  ResSet C = ⊕ᴰSet isSetFin (Alt C)

  -- An instance that fires pins the type's head.  This is the route's
  -- `into`, and it is also how a non-matching instance is refuted.
  atNodeM : (o : COp) (P : arities CSig o → Cls) → MatchTy o P ⊢ NodeAt o
  atNodeM ιOp   P ι       _ = nodeAtOf ι
  atNodeM ιOp   P (lst _) ()
  atNodeM ιOp   P (_ ⇒ _) ()
  atNodeM lstOp P ι       ()
  atNodeM lstOp P (lst a) _ = nodeAtOf (lst a)
  atNodeM lstOp P (_ ⇒ _) ()
  atNodeM arrOp P ι       ()
  atNodeM arrOp P (lst _) ()
  atNodeM arrOp P (a ⇒ b) _ = nodeAtOf (a ⇒ b)

  -- The slots of an instance's node: one premise per argument of the head,
  -- each at the class the context names.  Independent of the splitting --
  -- there is no binder here, so `⊗ᴰ` is used in its constant case.
  Slots : (o : COp) (P : arities CSig o → Cls) → NodeArgs ℓ-zero o
  Slots o P ms a = ResSet (P a)

  rollM : (o : COp) (P : arities CSig o → Cls)
    → ⊗ᴰ o (Slots o P) ⊢ MatchTy o P
  rollM ιOp   P m (ms , Eq.refl , ws) = tt
  rollM lstOp P m (ms , Eq.refl , ws) = ws theElem
  rollM arrOp P m (ms , Eq.refl , ws) = ws theDom , ws theCod

  unrollM : (o : COp) (P : arities CSig o → Cls)
    → MatchTy o P & NodeAt o ⊢ ⊗ᴰ o (Slots o P)
  unrollM ιOp   P m (u , (ms , Eq.refl)) = node-mk {ms = ms} λ ()
  unrollM lstOp P m (r , (ms , Eq.refl)) =
    node-mk {ms = ms} λ where theElem → r
  unrollM arrOp P m (p , (ms , Eq.refl)) =
    node-mk {ms = ms} λ where
      theDom → p .fst
      theCod → p .snd

  open Subtype {X = Cls} isSetCls (λ _ → 0) hiding (_<_) public

  -- The premise at argument `a` sits at a proper subtype, which is the
  -- whole of the guard's obligation.
  module _ where
    open Subtype {X = Cls} isSetCls (λ _ → 0) using (_<_)

    callSlot : {C C' : Cls} (o : COp) (ms : interpIn o ↓M) (a : arities CSig o)
      → (C' , ms a) < (C , op o ms)
    callSlot ιOp   ms ()
    callSlot {C = C} {C' = C'} lstOp ms theElem =
      callElem {x = C} {x' = C'} (ms theElem)
    callSlot {C = C} {C' = C'} arrOp ms theDom =
      callDom {x = C} {x' = C'} (ms theDom) (ms theCod)
    callSlot {C = C} {C' = C'} arrOp ms theCod =
      callCod {x = C} {x' = C'} (ms theDom) (ms theCod)


  -- The resolver, for whatever answer, once a way of picking among the
  -- instances is supplied.  Everything above `Pick` is answer-agnostic and
  -- coherence-agnostic; `Pick` is where both enter.
  module Check (𝒯 : AnswerFunctor) where

    open Combinators 𝒯 srt order public

    Pick : Type _
    Pick = (C : Cls)
      → ty (&ᴰSet (λ i → Ans (Alt C i))) ⊢ ty (Ans (ResSet C))

    module _ (pick : Pick) where

      step : Step ResSet
      step C = look nodeCover branch
        where
        nodeAns : (o : COp) (P : arities CSig o → Cls)
          → ▷ (AnsFam ResSet) C & NodeAt o
          ⊢ ty (Ans (⊗ᴰSet o (Slots o P)))
        nodeAns o P m (β , (ms , Eq.refl)) =
          Ans-node o (preciseC o) {As = Slots o P} {ms = ms}
            λ a → callAt (P a) (callSlot {C = C} {C' = P a} o ms a) β

        -- an instance whose head is not the type's head cannot fire, and
        -- the cover's `disjoint` is what says so
        refute : (o : COp) (i : Inst C) → (head C i Eq.≡ o → ⊥)
          → NodeAt o ⊢ DecTy (ty (Alt C i))
        refute o i ne =
          dec-no ∘⊢ ⇒-intro
            (nodeCover .disjoint (head C i) o ne
             ∘⊢ ((atNodeM (head C i) (ctx C i) ∘⊢ π₂) ,& π₁))

        alt : (o : COp) (i : Inst C)
          → (head C i Eq.≡ o) Sum.⊎ ((head C i Eq.≡ o) → ⊥)
          → ▷ (AnsFam ResSet) C & NodeAt o ⊢ ty (Ans (Alt C i))
        alt o i (Sum.inr ne) = Ans-ofDec ∘⊢ refute o i ne ∘⊢ π₂
        alt .(head C i) i (Sum.inl Eq.refl) =
          Ans-map& (rollM (head C i) (ctx C i) ∘⊢ π₁)
                   (unrollM (head C i) (ctx C i))
          ∘⊢ (nodeAns (head C i) (ctx C i) ,& π₂)

        branch : (o : COp)
          → ▷ (AnsFam ResSet) C & NodeAt o ⊢ ty (Ans (ResSet C))
        branch o =
          pick C ∘⊢ &ᴰ-intro λ i → alt o i (decCOp (head C i) o)

      resolver : Checker ResSet
      resolver = fix step

    -- Picking by routing.  Needs a coherent table -- and needs it exactly
    -- where the header says it does, in `disjoint`.
    module Routed (coh : Coherent T) (com : CommittingAnswer 𝒯) where
      open CommittingAnswer com

      RB : (C : Cls) → Maybe (Inst C) → TheoryTy ℓ-zero tyS
      RB C nothing = &[ i ∈ Inst C ] ¬Ty (NodeAt (head C i))
      RB C (just i) = NodeAt (head C i)

      private
        -- transporting a node along a head equation, rather than matching
        -- `Eq.refl` on two neutral operations, which is stuck without K
        hit : (C : Cls) (i : Inst C) (o : COp) (t : Typ)
          → head C i Eq.≡ o → NodeAt o t → NodeAt (head C i) t
        hit C i o t Eq.refl n = n

        rcov : (C : Cls) → Cover (Maybe (Inst C)) (RB C)
        rcov C .total t _ =
          onFound (findFin λ i → decCOp (head C i) (headOf t))
          where
          onFound : (Σ[ i ∈ Inst C ] (head C i Eq.≡ headOf t))
                    Sum.⊎ ((i : Inst C) → head C i Eq.≡ headOf t → ⊥)
                  → Σ[ v ∈ Maybe (Inst C) ] RB C v t
          onFound (Sum.inl (i , e)) = just i , hit C i (headOf t) t e (nodeAtOf t)
          onFound (Sum.inr miss) = nothing , λ i n →
            nodeCover .disjoint (head C i) (headOf t) (miss i) t (n , nodeAtOf t)
        rcov C .disjoint nothing nothing ne = Empty.rec (ne Eq.refl)
        rcov C .disjoint nothing (just j) ne t (f , n) = f j n
        rcov C .disjoint (just i) nothing ne t (n , f) = f i n
        rcov C .disjoint (just i) (just j) ne =
          onHeads (decCOp (head C i) (head C j))
          where
          -- COHERENCE, cashed in.  Two instances that match the same type
          -- have the same head, and a coherent table has at most one
          -- instance per head, so they are the same instance.
          onHeads : (head C i Eq.≡ head C j) Sum.⊎ ((head C i Eq.≡ head C j) → ⊥)
            → NodeAt (head C i) & NodeAt (head C j) ⊢ ⊥Ty
          onHeads (Sum.inl e) =
            Empty.rec (ne (Eq.pathToEq (cong just (Eq.eqToPath (coh C i j e)))))
          onHeads (Sum.inr hne) = nodeCover .disjoint (head C i) (head C j) hne

      route : (C : Cls) → Route (λ i → ty (Alt C i)) ℓ-zero
      route C .Route.B = RB C
      route C .Route.cov = rcov C
      route C .Route.into i = atNodeM (head C i) (ctx C i)

      routed : Pick
      routed C = Ans-route isSetFin (Alt C) (route C) decFinEq

    -- ...and picking by enumeration.  No route, no coherence, no
    -- commitment: every instance is asked and every answer kept.  Only a
    -- covariant answer can do it.
    module Ambiguous (cov : CovariantAnswer 𝒯) where
      ambig : Pick
      ambig C = CovCombinators.Ans-anyFin 𝒯 cov (Alt C) λ i → π i


  -- THE DICTIONARY.  A derivation is a tree of instance choices, and that
  -- tree is what a compiler passes at runtime.  `dictOf` reads it off.
  toDict : (C : Cls) (t : Typ) → ResTy C t → Dict
  dictArgs : (o : COp) (P : arities CSig o → Cls) (t : Typ)
    → MatchTy o P t → List Dict

  toDict C t (i , mt) = dict (toℕ i) (dictArgs (head C i) (ctx C i) t mt)

  dictArgs ιOp   P ι       _ = []
  dictArgs ιOp   P (lst _) ()
  dictArgs ιOp   P (_ ⇒ _) ()
  dictArgs lstOp P ι       ()
  dictArgs lstOp P (lst a) r = toDict (P theElem) a r ∷ []
  dictArgs lstOp P (_ ⇒ _) ()
  dictArgs arrOp P ι       ()
  dictArgs arrOp P (lst _) ()
  dictArgs arrOp P (a ⇒ b) p =
    toDict (P theDom) a (p .fst) ∷ toDict (P theCod) b (p .snd) ∷ []

  dictAction : (C : Cls) → SemanticAction (ty (ResSet C)) Dict
  dictAction C t d = toDict C t d , tt

  -- The front end, at `Dec`.  It needs `Coherent T` because the routed
  -- resolver does, which is the point: you cannot get a decision procedure
  -- out of an incoherent table, and the failure is static.
  --
  -- This lives in the client rather than in the tests: a client exports
  -- its front end and a test calls it.
  module Front (coh : Coherent T) where
    module CD = Check D.DecAnswer

    decRes : CD.Checker ResSet
    decRes = CD.resolver (CD.Routed.routed coh D.DecCommitting)

    resolve : Cls → Typ → Maybe Dict
    resolve C = observe (decRes C) (semact-dec (dictAction C))
