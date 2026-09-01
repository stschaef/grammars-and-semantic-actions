{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Type checker for the annotated lambda calculus; intrinsically typed, so
   also an elaborator: `Der (Γ , A) t` pairs a core term with its erasure proof. -}
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
open import Cubical.Relation.Nullary.Properties using (isProp¬)
import Cubical.Data.Sum as Sum
open import Cubical.Data.Sum using (isProp⊎)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Annotated.Guard public

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

Jdg : Type ℓ-zero
Jdg = Ctx × Ty

isSetIdx : isSet Jdg
isSetIdx = isSetΣ isSetCtx λ _ → isSetTyp

ArrHead : Ty → Ty → Type ℓ-zero
ArrHead A B = IsArr A × (dom A ≡ B)

isPropArrHead : (A B : Ty) → isProp (ArrHead A B)
isPropArrHead A B = isProp× (isPropIsArr A) (isSetTyp _ _)

ArrSet : Ty → Ty → TheorySet ℓ-zero nm
ArrSet A B = (λ _ → ArrHead A B) , λ _ → isProp→isSet (isPropArrHead A B)

decArr : (A B : Ty) → Dec (ArrHead A B)
decArr ι B = no fst
decArr (B' ⇒ C) B = onDom (discreteTy B' B)
  where
  onDom : Dec (B' ≡ B) → Dec (ArrHead (B' ⇒ C) B)
  onDom (yes p) = yes (tt , p)
  onDom (no ¬p) = no λ z → ¬p (z .snd)

decArrHead : (A B : Ty) → Decidable (ty (ArrSet A B))
decArrHead A B = dec-fromDec λ _ → decArr A B

-- Positional `var` premise; summands are mutually exclusive, so shadowing
-- resolves to the innermost binding and `Lookup` stays a proposition.
Lookup : Ctx → Ty → ℕ → Type ℓ-zero
Lookup [] A x = Empty.⊥
Lookup ((y , B) ∷ Γ) A x =
  ((x ≡ y) × (A ≡ B)) Sum.⊎ ((x ≡ y → Empty.⊥) × Lookup Γ A x)

deBruijn : (Γ : Ctx) (A : Ty) (x : ℕ) → Lookup Γ A x → ℕ
deBruijn ((y , B) ∷ Γ) A x (Sum.inl _) = 0
deBruijn ((y , B) ∷ Γ) A x (Sum.inr (_ , v)) = ℕ.suc (deBruijn Γ A x v)


isPropLookup : (Γ : Ctx) (A : Ty) (x : ℕ) → isProp (Lookup Γ A x)
isPropLookup [] A x = λ ()
isPropLookup ((y , B) ∷ Γ) A x =
  isProp⊎ (isProp× (isSetℕ _ _) (isSetTyp _ _))
          (isProp× (isProp¬ _) (isPropLookup Γ A x))
          (λ hit miss → miss .fst (hit .fst))

Look : Ctx → Ty → TheoryTy ℓ-zero nm
Look Γ A = Lookup Γ A

LookSet : Ctx → Ty → TheorySet ℓ-zero nm
LookSet Γ A = Look Γ A , λ x → isProp→isSet (isPropLookup Γ A x)

decLookup : (Γ : Ctx) (A : Ty) (x : ℕ) → Dec (Lookup Γ A x)
decLookup [] A x = no λ ()
decLookup ((y , B) ∷ Γ) A x = onName (discreteℕ x y) (discreteTy A B)
  where
  onTail : (x ≡ y → Empty.⊥) → Dec (Lookup Γ A x)
    → Dec (Lookup ((y , B) ∷ Γ) A x)
  onTail ne (yes v) = yes (Sum.inr (ne , v))
  onTail ne (no ¬v) = no λ where
    (Sum.inl hit) → ne (hit .fst)
    (Sum.inr miss) → ¬v (miss .snd)

  onName : Dec (x ≡ y) → Dec (A ≡ B) → Dec (Lookup ((y , B) ∷ Γ) A x)
  onName (yes p) (yes q) = yes (Sum.inl (p , q))
  onName (yes p) (no ¬q) = no λ where
    (Sum.inl hit) → ¬q (hit .snd)
    (Sum.inr miss) → miss .fst p
  onName (no ¬p) _ = onTail ¬p (decLookup Γ A x)

decLook : (Γ : Ctx) (A : Ty) → Decidable (Look Γ A)
decLook Γ A = dec-fromDec (decLookup Γ A)

-- `cvar` carries a `Lookup`, not a numeral: with a numeral, shadowed
-- contexts give two core terms with the same erasure, breaking propositionality.
data Core : Ctx → Ty → Type ℓ-zero where
  cvar : {Γ : Ctx} {A : Ty} (x : ℕ) → Lookup Γ A x → Core Γ A
  capp : {Γ : Ctx} {A B : Ty} → Core Γ (B ⇒ A) → Core Γ B → Core Γ A
  clam : {Γ : Ctx} {A B : Ty} (x : ℕ) → Core ((x , B) ∷ Γ) A → Core Γ (B ⇒ A)

erase : {Γ : Ctx} {A : Ty} → Core Γ A → ATm
erase (cvar x _) = avar x
erase (capp {B = B} f a) = aapp B (erase f) (erase a)
erase (clam {B = B} x t) = alam x B (erase t)

arrEta : {B : Ty} (A : Ty) → ArrHead A B → A ≡ B ⇒ cod A
arrEta ι (h , _) = Empty.rec h
arrEta (B' ⇒ C) (_ , p) = cong (_⇒ C) p

eraseSubst : {Γ : Ctx} {A A' : Ty} (e : A ≡ A') (c : Core Γ A)
  → erase (subst (Core Γ) e c) ≡ erase c
eraseSubst {Γ = Γ} e c i = erase (subst-filler (Core Γ) e c (~ i))

Der : Jdg → TheoryTy ℓ-zero tm
Der (Γ , A) t = Σ[ c ∈ Core Γ A ] (erase c ≡ t)

-- The erasure fibre, computed by recursion on the source.
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

graph : {Γ : Ctx} {A : Ty} (c : Core Γ A) → Der⁻ (Γ , A) (erase c)
graph (cvar x v) = v
graph (capp f a) = graph f , graph a
graph (clam x c) = (tt , refl) , graph c

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

-- `Der` is a retract of the computed fibre, not a truncation of it.
isPropDer : (i : Jdg) (t : ATm) → isProp (Der i t)
isPropDer i t =
  isOfHLevelRetract 1 (into i t) (from i t) (fromInto i t) (isPropDer⁻ i t)

DerSet : Jdg → TheorySet ℓ-zero tm
DerSet i = Der i , λ t → isProp→isSet (isPropDer i t)

Slots : (o : AOp) → Jdg → NodeArgs ℓ-zero o
Slots varOp (Γ , A) ms theVar = LookSet Γ A
Slots (appOp B) (Γ , A) ms theFun = DerSet (Γ , B ⇒ A)
Slots (appOp B) (Γ , A) ms theArg = DerSet (Γ , B)
Slots (lamOp B) (Γ , A) ms theBinder = ArrSet A B
Slots (lamOp B) (Γ , A) ms theBody = DerSet ((ms theBinder , B) ∷ Γ , cod A)

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

  -- Unroll goes through the fibre; the round trip runs only to carry a refutation.
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
