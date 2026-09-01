{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Bidirectional checker for unannotated lambda calculus.  `Syn Γ t =
   ⨁[ A ∈ Ty ] Chk (Γ , A) t`; `Chk` is by recursion on the term (an
   indexed `data` hits `SplitError.UnificationStuck` without K). -}
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
open import Theory.Instances.Annotated.Typing
  using (ArrHead ; isPropArrHead ; decArr ; Lookup ; isPropLookup ; decLookup)

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


Look : Ctx → Ty → TheoryTy ℓ-zero nm
Look Γ A = Lookup Γ A

LookSet : Ctx → Ty → TheorySet ℓ-zero nm
LookSet Γ A = Look Γ A , λ x → isProp→isSet (isPropLookup Γ A x)

decLook : (Γ : Ctx) (A : Ty) → Decidable (Look Γ A)
decLook Γ A = dec-fromDec (decLookup Γ A)


ArrCod : Ty → Ty → Type ℓ-zero
ArrCod C A = IsArr C × (cod C ≡ A)


isPropArrCod : (C A : Ty) → isProp (ArrCod C A)
isPropArrCod C A = isProp× (isPropIsArr C) (isSetTyp _ _)

ArrSet : Ty → Ty → TheorySet ℓ-zero nm
ArrSet A B = (λ _ → ArrHead A B) , λ _ → isProp→isSet (isPropArrHead A B)

ArrCodSet : Ty → Ty → TheorySet ℓ-zero tm
ArrCodSet C A = (λ _ → ArrCod C A) , λ _ → isProp→isSet (isPropArrCod C A)

decArrHead : (A B : Ty) → Decidable (ty (ArrSet A B))
decArrHead A B = dec-fromDec λ _ → decArr A B

decCod : (C A : Ty) → Dec (ArrCod C A)
decCod ι A = no fst
decCod (B ⇒ C) A = onCod (discreteTy C A)
  where
  onCod : Dec (C ≡ A) → Dec (ArrCod (B ⇒ C) A)
  onCod (yes p) = yes (tt , p)
  onCod (no ¬p) = no λ z → ¬p (z .snd)

decArrCod : (C A : Ty) → Decidable (ty (ArrCodSet C A))
decArrCod C A = dec-fromDec λ _ → decCod C A

Chk : Ctx → Ty → BTm → Type ℓ-zero
Chk Γ A (bvar x) = Lookup Γ A x
Chk Γ A (bapp f a) =
  Σ[ C ∈ Ty ] (ArrCod C A × Chk Γ C f × Chk Γ (dom C) a)
Chk Γ A (blam x B t) = ArrHead A B × Chk ((x , B) ∷ Γ) (cod A) t

-- Untrusted candidate: never looks at an application’s argument; only
-- `soundInfer` is proved about it.
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

soundInfer : (Γ : Ctx) (A : Ty) (t : BTm) → Chk Γ A t → infer Γ t ≡ just A
soundInfer Γ A (bvar x) w = lookSound Γ A x w
soundInfer Γ A (bapp f a) (C , (isa , e) , df , da) =
    cong codOf (soundInfer Γ C f df)
  ∙ codOfArr C isa
  ∙ cong just e
soundInfer Γ A (blam x B t) ((isa , e) , dt) =
    cong (arrow B) (soundInfer ((x , B) ∷ Γ) (cod A) t dt)
  ∙ cong just (cong (_⇒ cod A) (sym e) ∙ arrEta A isa)

uniqueSyn : (Γ : Ctx) (A A' : Ty) (t : BTm) → Chk Γ A t → Chk Γ A' t → A ≡ A'
uniqueSyn Γ A A' t d d' =
  just-inj A A' (sym (soundInfer Γ A t d) ∙ soundInfer Γ A' t d')

private
  isPropΣ' : {ℓb ℓp : Level} {B : Type ℓb} {P : B → Type ℓp}
    → (∀ b b' → P b → P b' → b ≡ b') → (∀ b → isProp (P b)) → isProp (Σ B P)
  isPropΣ' u pp (b , p) (b' , p') =
    ΣPathP (u b b' p p' , isProp→PathP (λ i → pp (u b b' p p' i)) p p')

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

SynSet : Ctx → TheorySet ℓ-zero tm
SynSet Γ = ⊕ᴰSet isSetTyp (ChkSet Γ)

Mode : Type ℓ-zero
Mode = Ctx Sum.⊎ (Ctx × Ty)

pattern synM Γ = Sum.inl Γ
pattern chkM Γ A = Sum.inr (Γ , A)

isSetMode : isSet Mode
isSetMode = isSet⊎ isSetCtx (isSetΣ isSetCtx λ _ → isSetTyp)

-- `Chk` is the smaller mode: `Syn` is a sum of `Chk`s at the same term.
rankM : Mode → ℕ
rankM (synM _) = 1
rankM (chkM _ _) = 0

Jdg : Mode → TheorySet ℓ-zero tm
Jdg (synM Γ) = SynSet Γ
Jdg (chkM Γ A) = ChkSet Γ A

VarSlots : Ctx → Ty → NodeArgs ℓ-zero varOp
VarSlots Γ A ms theVar = LookSet Γ A

LamSlots : (B : Ty) → Ctx → Ty → NodeArgs ℓ-zero (lamOp B)
LamSlots B Γ A ms theBinder = ArrSet A B
LamSlots B Γ A ms theBody = ChkSet ((ms theBinder , B) ∷ Γ) (cod A)

-- `app`’s side condition has no slot of its own, so it rides with the
-- function slot (`Ans-&&`, per `Combinator/Core`’s header).
AppSlots : Ctx → Ty → Ty → NodeArgs ℓ-zero appOp
AppSlots Γ A C ms theFun = ChkSet Γ C &Set ArrCodSet C A
AppSlots Γ A C ms theArg = ChkSet Γ (dom C)

AppAlt : Ctx → Ty → Ty → TheorySet ℓ-zero tm
AppAlt Γ A C = ⊗ᴰSet appOp (AppSlots Γ A C)

AppSum : Ctx → Ty → TheorySet ℓ-zero tm
AppSum Γ A = ⊕ᴰSet isSetTyp (AppAlt Γ A)

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
  candidate g Γ .disjoint = clsDisjoint (g Γ) λ v t e → Eq.eqToPath e

synRoute : (Γ : Ctx) → Route (λ A → ty (ChkSet Γ A)) ℓ-zero
synRoute Γ .Route.B v t = infer Γ t Eq.≡ v
synRoute Γ .Route.cov = candidate infer Γ
synRoute Γ .Route.into A t d = Eq.pathToEq (soundInfer Γ A t d)

appRoute : (Γ : Ctx) (A : Ty) → Route (λ C → ty (AppAlt Γ A C)) ℓ-zero
appRoute Γ A .Route.B v t = inferFun Γ t Eq.≡ v
appRoute Γ A .Route.cov = candidate inferFun Γ
appRoute Γ A .Route.into C _ (ms , Eq.refl , ws) =
  Eq.pathToEq (soundInfer Γ C (ms theFun) (ws theFun .fst))


module Check (𝒯 : AnswerFunctor) (com : CommittingAnswer 𝒯) where

  open Subterm {X = Mode} isSetMode rankM hiding (_<_) public
  open Combinators 𝒯 srt order public
  open CommittingAnswer com public

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
