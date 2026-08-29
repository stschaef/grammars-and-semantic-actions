{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A BIDIRECTIONAL type checker for the unannotated lambda calculus, and
   the identification `Annotated/Typing`'s header predicted:

     `Route`'s obligation, for bidirectional typing, IS UNIQUENESS OF
     SYNTHESIS.

   `Annotated` carries the argument type on the application node, and that
   annotation is the only reason its rule is syntax-directed.  Delete it
   and checking an application reads

     Γ ⊢ f a ⇐ A   iff   ∃C. Γ ⊢ f ⇐ C, C is an arrow with cod A,
                              Γ ⊢ a ⇐ dom C

   -- an indexed sum over `Ty`, which is infinite.  A checker cannot ask
   every alternative, and `Ans-route` is the field that says it need not:
   a `Route` covers the model by `Maybe Ty` -- "the function synthesises
   `C`", or "it synthesises nothing" -- and only the named cell is queried.

   TWO MODES, and the mode change.  The family is indexed by

     Mode = Ctx ⊎ (Ctx × Ty)          `Syn Γ` and `Chk (Γ , A)`

   with `Syn Γ t = ⊕[ A ∈ Ty ] Chk (Γ , A) t` -- on the nose, because
   `Ans-route` produces an answer at a `⊕ᴰSet` and not at something
   isomorphic to one.  So synthesis at `t` calls checking at `t`: the same
   term, a different mode.  `Guard`'s `modeStep` is that step and
   `ilexOrder`'s `rank` is what makes it well-founded; `Chk` gets rank 0
   and `Syn` rank 1, which is forced by the direction of the call.

   WHERE THE THEOREM LIVES.  A `Route` is three things: cells `B`, a
   `Cover`, and `into : Φ y ⊢ B (just y)`.  Choose the cells to be

     B v t  =  (infer Γ t Eq.≡ v)

   for the ordinary recursive candidate `infer`.  Then

     * `total`    is `(infer Γ t , Eq.refl)`: the search that names a
                  candidate, and it always terminates.
     * `disjoint` is injectivity of a function: a term cannot have two
                  candidates.
     * `into`     is SOUNDNESS OF INFERENCE -- `Γ ⊢ t ⇐ A` implies
                  `infer Γ t ≡ just A` -- and composing it with `disjoint`
                  gives, verbatim,

                     Γ ⊢ t ⇐ A → Γ ⊢ t ⇐ A' → A ≡ A'

                  which is `uniqueSyn` below.  PROVED, by induction on the
                  term; nothing is postulated.

   So the obligation is uniqueness of synthesis, factored through a
   candidate function.  That factoring is not a dodge -- it is what makes
   `infer` UNTRUSTED: completeness of `infer` is never proved and never
   needed, because the framework re-verifies the candidate with the
   recursive answers.  `infer` names a type; the checker decides it.

   `Chk` is defined by RECURSION on the term, not as an indexed `data`:
   the latter makes every branch a `SplitError.UnificationStuck` without K.
   That it is a *proposition* is a theorem here rather than a definitional
   fact, and the theorem it needs is again uniqueness -- the existential's
   witness is unique, so `Σ` collapses.

   Nothing below mentions `Dec`, `Maybe` or `ND`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Bidir.Typing where

open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.List.Properties using (isOfHLevelList)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Maybe.Properties using (isOfHLevelMaybe ; just-inj)
open import Cubical.Data.Nat using (ℕ ; isSetℕ ; discreteℕ)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd ; ΣPathP)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no)
import Cubical.Data.Sum as Sum
open import Cubical.Data.Sum using (isProp⊎ ; isSet⊎)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Bidir.Guard public

-- Contexts and the candidate-free part of lookup.
Ctx : Type ℓ-zero
Ctx = List (ℕ × Ty)

isSetCtx : isSet Ctx
isSetCtx = isOfHLevelList 0 (isSetΣ isSetℕ λ _ → isSetTyp)

private
  hitOr : {ℓp : Level} {P : Type ℓp} → Dec P → Ty → Maybe Ty → Maybe Ty
  hitOr (yes _) B r = just B
  hitOr (no _) B r = r

lookC : Ctx → ℕ → Maybe Ty
lookC [] x = nothing
lookC ((y , B) ∷ Γ) x = hitOr (discreteℕ x y) B (lookC Γ x)

-- The `var` rule's premise, carrying the position: a chain of "not here"
-- steps ending in a hit.  Mutually exclusive summands, so it is a
-- proposition, and shadowing resolves to the innermost binding.
Lookup : Ctx → Ty → ℕ → Type ℓ-zero
Lookup [] A x = Empty.⊥
Lookup ((y , B) ∷ Γ) A x =
  ((x ≡ y) × (A ≡ B)) Sum.⊎ ((x ≡ y → Empty.⊥) × Lookup Γ A x)

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

-- The two side conditions.  `ArrHead A B` is the `lam` rule's -- "the type
-- being checked against is an arrow with domain `B`" -- and `ArrCod C A`
-- is the `app` rule's, "the function's synthesised type is an arrow with
-- codomain `A`".  Both are propositions and both are decidable, which is
-- all a slot asks of them.
ArrHead : Ty → Ty → Type ℓ-zero
ArrHead A B = IsArr A × (dom A ≡ B)

ArrCod : Ty → Ty → Type ℓ-zero
ArrCod C A = IsArr C × (cod C ≡ A)

isPropArrHead : (A B : Ty) → isProp (ArrHead A B)
isPropArrHead A B = isProp× (isPropIsArr A) (isSetTyp _ _)

isPropArrCod : (C A : Ty) → isProp (ArrCod C A)
isPropArrCod C A = isProp× (isPropIsArr C) (isSetTyp _ _)

ArrSet : Ty → Ty → TheorySet ℓ-zero nm
ArrSet A B = (λ _ → ArrHead A B) , λ _ → isProp→isSet (isPropArrHead A B)

ArrCodSet : Ty → Ty → TheorySet ℓ-zero tm
ArrCodSet C A = (λ _ → ArrCod C A) , λ _ → isProp→isSet (isPropArrCod C A)

decArrHead : (A B : Ty) → Decidable (ty (ArrSet A B))
decArrHead ι B x _ = Sum.inr λ z → Empty.rec (z .fst)
decArrHead (B' ⇒ C) B x _ = onDom (discreteTy B' B)
  where
  onDom : Dec (B' ≡ B) → DecTy (ty (ArrSet (B' ⇒ C) B)) x
  onDom (yes p) = Sum.inl (tt , p)
  onDom (no ¬p) = Sum.inr λ z → Empty.rec (¬p (z .snd))

decArrCod : (C A : Ty) → Decidable (ty (ArrCodSet C A))
decArrCod ι A t _ = Sum.inr λ z → Empty.rec (z .fst)
decArrCod (B ⇒ C) A t _ = onCod (discreteTy C A)
  where
  onCod : Dec (C ≡ A) → DecTy (ty (ArrCodSet (B ⇒ C) A)) t
  onCod (yes p) = Sum.inl (tt , p)
  onCod (no ¬p) = Sum.inr λ z → Empty.rec (¬p (z .snd))

-- THE JUDGMENT.  Checking, by recursion on the term.  The application case
-- is the existential the annotation used to discharge.
Chk : Ctx → Ty → BTm → Type ℓ-zero
Chk Γ A (bvar x) = Lookup Γ A x
Chk Γ A (bapp f a) =
  Σ[ C ∈ Ty ] (ArrCod C A × Chk Γ C f × Chk Γ (dom C) a)
Chk Γ A (blam x B t) = ArrHead A B × Chk ((x , B) ∷ Γ) (cod A) t

-- THE CANDIDATE.  An ordinary recursive guess at the type of a term, and
-- deliberately not a checker: it never looks at an application's argument.
-- Nothing downstream trusts it -- only `soundInfer` is proved, and the
-- framework re-verifies whatever it names.
codOf : Maybe Ty → Maybe Ty
codOf nothing = nothing
codOf (just ι) = nothing
codOf (just (_ ⇒ C)) = just C

arrow : Ty → Maybe Ty → Maybe Ty
arrow B nothing = nothing
arrow B (just C) = just (B ⇒ C)

infer : Ctx → BTm → Maybe Ty
infer Γ (bvar x) = lookC Γ x
infer Γ (bapp f a) = codOf (infer Γ f)
infer Γ (blam x B t) = arrow B (infer ((x , B) ∷ Γ) t)

-- ...and the candidate at the FUNCTION of an application, which is the
-- cell index of the route the `app` rule needs.
inferFun : Ctx → BTm → Maybe Ty
inferFun Γ (bvar _) = nothing
inferFun Γ (bapp f a) = infer Γ f
inferFun Γ (blam _ _ _) = nothing

private
  arrEta : (A : Ty) → IsArr A → (dom A ⇒ cod A) ≡ A
  arrEta ι ()
  arrEta (B ⇒ C) _ = refl

  codOfArr : (C : Ty) → IsArr C → codOf (just C) ≡ just (cod C)
  codOfArr ι ()
  codOfArr (B ⇒ C) _ = refl

  lookSound : (Γ : Ctx) (A : Ty) (x : ℕ) → Lookup Γ A x → lookC Γ x ≡ just A
  lookSound ((y , B) ∷ Γ) A x w = go (discreteℕ x y) w
    where
    go : (d : Dec (x ≡ y)) → Lookup ((y , B) ∷ Γ) A x
       → hitOr d B (lookC Γ x) ≡ just A
    go (yes p) (Sum.inl (_ , q)) = cong just (sym q)
    go (yes p) (Sum.inr (ne , _)) = Empty.rec (ne p)
    go (no ¬p) (Sum.inl (p , _)) = Empty.rec (¬p p)
    go (no ¬p) (Sum.inr (_ , w')) = lookSound Γ A x w'

-- SOUNDNESS OF INFERENCE: a term that checks at `A` has candidate `A`.
-- This is the route's `into`, and it is the only theorem in this file.
soundInfer : (Γ : Ctx) (A : Ty) (t : BTm) → Chk Γ A t → infer Γ t ≡ just A
soundInfer Γ A (bvar x) w = lookSound Γ A x w
soundInfer Γ A (bapp f a) (C , (isa , e) , df , da) =
    cong codOf (soundInfer Γ C f df)
  ∙ codOfArr C isa
  ∙ cong just e
soundInfer Γ A (blam x B t) ((isa , e) , dt) =
    cong (arrow B) (soundInfer ((x , B) ∷ Γ) (cod A) t dt)
  ∙ cong just (cong (_⇒ cod A) (sym e) ∙ arrEta A isa)

-- UNIQUENESS OF SYNTHESIS, which is what the route's obligation amounts
-- to once `into` and `disjoint` are composed.  Proved, not assumed.
uniqueSyn : (Γ : Ctx) (A A' : Ty) (t : BTm) → Chk Γ A t → Chk Γ A' t → A ≡ A'
uniqueSyn Γ A A' t d d' =
  just-inj A A' (sym (soundInfer Γ A t d) ∙ soundInfer Γ A' t d')

private
  isPropΣ' : {ℓb ℓp : Level} {B : Type ℓb} {P : B → Type ℓp}
    → (∀ b b' → P b → P b' → b ≡ b') → (∀ b → isProp (P b)) → isProp (Σ B P)
  isPropΣ' u pp (b , p) (b' , p') =
    ΣPathP (u b b' p p' , isProp→PathP (λ i → pp (u b b' p p' i)) p p')

-- ...and the corollary that makes the judgment a proposition: the
-- existential's witness is pinned by uniqueness, so the `Σ` collapses.
-- An unannotated term still has at most one derivation at a type.
isPropChk : (Γ : Ctx) (A : Ty) (t : BTm) → isProp (Chk Γ A t)
isPropChk Γ A (bvar x) = isPropLookup Γ A x
isPropChk Γ A (bapp f a) = isPropΣ' same fibre
  where
  fibre : (C : Ty) → isProp (ArrCod C A × Chk Γ C f × Chk Γ (dom C) a)
  fibre C = isProp× (isPropArrCod C A)
    (isProp× (isPropChk Γ C f) (isPropChk Γ (dom C) a))

  same : (C C' : Ty)
    → ArrCod C A × Chk Γ C f × Chk Γ (dom C) a
    → ArrCod C' A × Chk Γ C' f × Chk Γ (dom C') a
    → C ≡ C'
  same C C' p p' = uniqueSyn Γ C C' f (p .snd .fst) (p' .snd .fst)
isPropChk Γ A (blam x B t) =
  isProp× (isPropArrHead A B) (isPropChk ((x , B) ∷ Γ) (cod A) t)

ChkSet : Ctx → Ty → TheorySet ℓ-zero tm
ChkSet Γ A = Chk Γ A , λ t → isProp→isSet (isPropChk Γ A t)

-- SYNTHESIS, on the nose as the indexed sum.  `Ans-route` answers a
-- `⊕ᴰSet` and nothing isomorphic to one, so this is a definition and not a
-- characterisation.
SynSet : Ctx → TheorySet ℓ-zero tm
SynSet Γ = ⊕ᴰSet isSetTyp (ChkSet Γ)

-- The index of the mutually recursive family: one component per mode.
Mode : Type ℓ-zero
Mode = Ctx Sum.⊎ (Ctx × Ty)

pattern synM Γ = Sum.inl Γ
pattern chkM Γ A = Sum.inr (Γ , A)

isSetMode : isSet Mode
isSetMode = isSet⊎ isSetCtx (isSetΣ isSetCtx λ _ → isSetTyp)

-- `Chk` is the smaller mode, because `Syn` is a sum of `Chk`s at the very
-- same term.  See `Guard`'s header.
rankM : Mode → ℕ
rankM (synM _) = 1
rankM (chkM _ _) = 0

Jdg : Mode → TheorySet ℓ-zero tm
Jdg (synM Γ) = SynSet Γ
Jdg (chkM Γ A) = ChkSet Γ A

-- The rules, as the slots of their nodes.  `app`'s slots are additionally
-- parameterised by the synthesised type `C` -- that parameter is the sum's
-- index, and the whole point.
VarSlots : Ctx → Ty → NodeArgs ℓ-zero varOp
VarSlots Γ A ms theVar = LookSet Γ A

LamSlots : (B : Ty) → Ctx → Ty → NodeArgs ℓ-zero (lamOp B)
LamSlots B Γ A ms theBinder = ArrSet A B
LamSlots B Γ A ms theBody = ChkSet ((ms theBinder , B) ∷ Γ) (cod A)

-- The `app` rule's side condition has no slot of its own -- a binary
-- operation has exactly two -- so it rides with the function, as
-- `Combinator/Core`'s header prescribes for `Ans-&&`.
AppSlots : Ctx → Ty → Ty → NodeArgs ℓ-zero appOp
AppSlots Γ A C ms theFun = ChkSet Γ C &Set ArrCodSet C A
AppSlots Γ A C ms theArg = ChkSet Γ (dom C)

AppAlt : Ctx → Ty → Ty → TheorySet ℓ-zero tm
AppAlt Γ A C = ⊗ᴰSet appOp (AppSlots Γ A C)

AppSum : Ctx → Ty → TheorySet ℓ-zero tm
AppSum Γ A = ⊕ᴰSet isSetTyp (AppAlt Γ A)

-- One level of unfolding, both ways, as `⊢`-terms.
rollVar : (Γ : Ctx) (A : Ty) → ⊗ᴰ varOp (VarSlots Γ A) ⊢ Chk Γ A
rollVar Γ A m (ms , Eq.refl , ws) = ws theVar

unrollVar : (Γ : Ctx) (A : Ty)
  → Chk Γ A & NodeAt varOp ⊢ ⊗ᴰ varOp (VarSlots Γ A)
unrollVar Γ A m (d , (ms , Eq.refl)) = node-mk {ms = ms} λ where theVar → d

rollLam : (B : Ty) (Γ : Ctx) (A : Ty)
  → ⊗ᴰ (lamOp B) (LamSlots B Γ A) ⊢ Chk Γ A
rollLam B Γ A m (ms , Eq.refl , ws) = ws theBinder , ws theBody

unrollLam : (B : Ty) (Γ : Ctx) (A : Ty)
  → Chk Γ A & NodeAt (lamOp B) ⊢ ⊗ᴰ (lamOp B) (LamSlots B Γ A)
unrollLam B Γ A m (d , (ms , Eq.refl)) = node-mk {ms = ms} λ where
  theBinder → d .fst
  theBody → d .snd

rollApp : (Γ : Ctx) (A : Ty) → ty (AppSum Γ A) ⊢ Chk Γ A
rollApp Γ A m (C , (ms , Eq.refl , ws)) =
  C , (ws theFun .snd , ws theFun .fst , ws theArg)

unrollApp : (Γ : Ctx) (A : Ty) → Chk Γ A & NodeAt appOp ⊢ ty (AppSum Γ A)
unrollApp Γ A m (d , (ms , Eq.refl)) =
  d .fst , node-mk {ms = ms} λ where
    theFun → d .snd .snd .fst , d .snd .fst
    theArg → d .snd .snd .snd

-- THE ROUTES.  Both have the same cells -- an equation on the candidate --
-- so `total` is the candidate itself and `disjoint` is injectivity of a
-- function.  `into` is `soundInfer`, and it is the content.
discreteEqTy : DiscreteEq Ty
discreteEqTy A B = onPath (discreteTy A B)
  where
  onPath : Dec (A ≡ B)
    → (A Eq.≡ B) Sum.⊎ ((A Eq.≡ B) → Empty.⊥)
  onPath (yes p) = Sum.inl (Eq.pathToEq p)
  onPath (no ¬p) = Sum.inr λ e → ¬p (Eq.eqToPath e)

private
  candidate : (g : Ctx → BTm → Maybe Ty) (Γ : Ctx)
    → Cover (Maybe Ty) (λ v t → g Γ t Eq.≡ v)
  candidate g Γ .total t _ = g Γ t , Eq.refl
  candidate g Γ .disjoint v v' ne t (e , e') =
    Empty.rec (ne (Eq.pathToEq (sym (Eq.eqToPath e) ∙ Eq.eqToPath e')))

synRoute : (Γ : Ctx) → Route (λ A → ty (ChkSet Γ A)) ℓ-zero
synRoute Γ .Route.B v t = infer Γ t Eq.≡ v
synRoute Γ .Route.cov = candidate infer Γ
synRoute Γ .Route.into A t d = Eq.pathToEq (soundInfer Γ A t d)

appRoute : (Γ : Ctx) (A : Ty) → Route (λ C → ty (AppAlt Γ A C)) ℓ-zero
appRoute Γ A .Route.B v t = inferFun Γ t Eq.≡ v
appRoute Γ A .Route.cov = candidate inferFun Γ
appRoute Γ A .Route.into C _ (ms , Eq.refl , ws) =
  Eq.pathToEq (soundInfer Γ C (ms theFun) (ws theFun .fst))


-- The checker, for whatever committing answer.
module Check (𝒯 : AnswerFunctor) (com : CommittingAnswer 𝒯) where

  open Subterm {X = Mode} isSetMode rankM hiding (_<_) public
  open Combinators 𝒯 srt order public
  open CommittingAnswer com public

  -- SYNTHESIS: route over the sum, and the recursive call is the mode
  -- change -- same term, rank 0 instead of rank 1.
  synStep : (Γ : Ctx) → ▷ (AnsFam Jdg) (synM Γ) ⊢ ty (Ans (SynSet Γ))
  synStep Γ =
    Ans-route isSetTyp (ChkSet Γ) (synRoute Γ) discreteEqTy
    ∘⊢ &ᴰ-intro λ A t β →
      callAt (chkM Γ A)
        (modeStep {x = synM Γ} {x' = chkM Γ A} {t = t} (0 , refl)) β

  varAns : (Γ : Ctx) (A : Ty)
    → ▷ (AnsFam Jdg) (chkM Γ A) & NodeAt varOp
    ⊢ ty (Ans (⊗ᴰSet varOp (VarSlots Γ A)))
  varAns Γ A _ (β , (ms , Eq.refl)) =
    Ans-node varOp (preciseB varOp) {As = VarSlots Γ A} {ms = ms}
      λ where theVar → Ans-ofDec (ms theVar) (decLook Γ A (ms theVar) tt)

  lamAns : (B : Ty) (Γ : Ctx) (A : Ty)
    → ▷ (AnsFam Jdg) (chkM Γ A) & NodeAt (lamOp B)
    ⊢ ty (Ans (⊗ᴰSet (lamOp B) (LamSlots B Γ A)))
  lamAns B Γ A _ (β , (ms , Eq.refl)) =
    Ans-node (lamOp B) (preciseB (lamOp B))
      {As = LamSlots B Γ A} {ms = ms}
      λ where
        theBinder → Ans-ofDec (ms theBinder) (decArrHead A B (ms theBinder) tt)
        theBody → callAt (chkM ((ms theBinder , B) ∷ Γ) (cod A))
          (callBody {x = chkM Γ A} {x' = chkM ((ms theBinder , B) ∷ Γ) (cod A)}
            (ms theBinder) B (ms theBody)) β

  -- APPLICATION: the sum, routed.  One alternative per candidate type of
  -- the function; the route says which, and only that one is asked.
  appAns : (Γ : Ctx) (A : Ty)
    → ▷ (AnsFam Jdg) (chkM Γ A) & NodeAt appOp ⊢ ty (Ans (AppSum Γ A))
  appAns Γ A _ (β , (ms , Eq.refl)) =
    Ans-route isSetTyp (AppAlt Γ A) (appRoute Γ A) discreteEqTy
      (op appOp ms) alt
    where
    alt : (C : Ty) → ty (Ans (AppAlt Γ A C)) (op appOp ms)
    alt C = Ans-node appOp (preciseB appOp) {As = AppSlots Γ A C} {ms = ms}
      λ where
        theFun → Ans-&& (ms theFun)
          ( callAt (chkM Γ C)
              (callFun {x = chkM Γ A} {x' = chkM Γ C} (ms theFun) (ms theArg)) β
          , Ans-ofDec (ms theFun) (decArrCod C A (ms theFun) tt) )
        theArg → callAt (chkM Γ (dom C))
          (callArg {x = chkM Γ A} {x' = chkM Γ (dom C)}
            (ms theFun) (ms theArg)) β

  chkBranch : (Γ : Ctx) (A : Ty) (o : BOp)
    → ▷ (AnsFam Jdg) (chkM Γ A) & NodeAt o ⊢ ty (Ans (ChkSet Γ A))
  chkBranch Γ A varOp =
    Ans-map& (rollVar Γ A ∘⊢ π₁) (unrollVar Γ A) ∘⊢ (varAns Γ A ,& π₂)
  chkBranch Γ A appOp =
    Ans-map& (rollApp Γ A ∘⊢ π₁) (unrollApp Γ A) ∘⊢ (appAns Γ A ,& π₂)
  chkBranch Γ A (lamOp B) =
    Ans-map& (rollLam B Γ A ∘⊢ π₁) (unrollLam B Γ A) ∘⊢ (lamAns B Γ A ,& π₂)

  step : Step Jdg
  step (synM Γ) = synStep Γ
  step (chkM Γ A) = look nodeCover (chkBranch Γ A)

  bidir : Checker Jdg
  bidir = fix step
