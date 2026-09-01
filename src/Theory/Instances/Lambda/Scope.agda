{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Scope checker for untyped lambda terms:
   `Scope Γ t = Σ[ d ∈ DBTm ] Names Γ d t`, elaborating to de Bruijn form. -}
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
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.List.Properties using (isOfHLevelList)
open import Cubical.Data.Sigma using (_×_ ; Σ-syntax ; ΣPathP ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Lambda.Guard Name isSetName public

Ctx : Type ℓ-zero
Ctx = List Name

isSetCtx : isSet Ctx
isSetCtx = isOfHLevelList 0 isSetName

data DBTm : Type ℓ-zero where
  dvar : ℕ → DBTm
  dapp : DBTm → DBTm → DBTm
  dlam : DBTm → DBTm

-- Positional membership ("slot n of Γ holds x") breaks propositionality
-- under shadowing; `At`.s summands are exclusive, so `n` is unique (`atUniq`).
At : Ctx → ℕ → TheoryTy ℓ-zero nm
At [] n x = Empty.⊥
At (y ∷ Γ) zero x = x ≡ y
At (y ∷ Γ) (suc n) x = (x ≡ y → Empty.⊥) × At Γ n x

InCtx : Ctx → TheoryTy ℓ-zero nm
InCtx Γ x = Σ[ n ∈ ℕ ] At Γ n x

deBruijn : (Γ : Ctx) (x : Name) → InCtx Γ x → ℕ
deBruijn Γ x = fst

private
  isPropNeq : {x y : Name} → isProp (x ≡ y → Empty.⊥)
  isPropNeq f g = funExt λ z → Empty.rec (f z)

isPropAt : (Γ : Ctx) (n : ℕ) (x : Name) → isProp (At Γ n x)
isPropAt [] n x = λ ()
isPropAt (y ∷ Γ) zero x = isSetName _ _
isPropAt (y ∷ Γ) (suc n) x = isProp× isPropNeq (isPropAt Γ n x)

atUniq : (Γ : Ctx) (n m : ℕ) (x : Name) → At Γ n x → At Γ m x → n ≡ m
atUniq [] n m x () _
atUniq (y ∷ Γ) zero zero x _ _ = refl
atUniq (y ∷ Γ) zero (suc m) x hit miss = Empty.rec (miss .fst hit)
atUniq (y ∷ Γ) (suc n) zero x miss hit = Empty.rec (miss .fst hit)
atUniq (y ∷ Γ) (suc n) (suc m) x a b = cong suc (atUniq Γ n m x (a .snd) (b .snd))

isPropInCtx : (Γ : Ctx) (x : Name) → isProp (InCtx Γ x)
isPropInCtx Γ x (n , a) (m , b) =
  ΣPathP (q , isProp→PathP (λ i → isPropAt Γ (q i) x) a b)
  where
  q : n ≡ m
  q = atUniq Γ n m x a b

InCtxSet : Ctx → TheorySet ℓ-zero nm
InCtxSet Γ = InCtx Γ , λ x → isProp→isSet (isPropInCtx Γ x)

decInCtx : (Γ : Ctx) → Decidable (InCtx Γ)
decInCtx [] x _ = Sum.inr λ where (n , ())
decInCtx (y ∷ Γ) x _ = onName (decName x y)
  where
  onTail : (x ≡ y → Empty.⊥) → DecTy (InCtx Γ) x → DecTy (InCtx (y ∷ Γ)) x
  onTail ne (Sum.inl (n , v)) = Sum.inl (suc n , (ne , v))
  onTail ne (Sum.inr ¬v) = Sum.inr λ where
    (zero , hit) → Empty.rec (ne hit)
    (suc n , miss) → ¬v (n , miss .snd)

  onName : Dec (x ≡ y) → DecTy (InCtx (y ∷ Γ)) x
  onName (yes p) = Sum.inl (zero , p)
  onName (no ¬p) = onTail ¬p (decInCtx Γ x tt)

-- Relational since `dlam` carries no binder name; recursion in both
-- arguments refutes mismatched heads on sight.
Names : Ctx → DBTm → TheoryTy ℓ-zero tm
Names Γ (dvar n) (tvar x) = At Γ n x
Names Γ (dvar n) (tapp _ _) = Empty.⊥
Names Γ (dvar n) (tlam _ _) = Empty.⊥
Names Γ (dapp d e) (tvar _) = Empty.⊥
Names Γ (dapp d e) (tapp t u) = Names Γ d t × Names Γ e u
Names Γ (dapp d e) (tlam _ _) = Empty.⊥
Names Γ (dlam d) (tvar _) = Empty.⊥
Names Γ (dlam d) (tapp _ _) = Empty.⊥
Names Γ (dlam d) (tlam x t) = Names (x ∷ Γ) d t

Scope : Ctx → TheoryTy ℓ-zero tm
Scope Γ t = Σ[ d ∈ DBTm ] Names Γ d t

isPropNames : (Γ : Ctx) (d : DBTm) (t : RawTm) → isProp (Names Γ d t)
isPropNames Γ (dvar n) (tvar x) = isPropAt Γ n x
isPropNames Γ (dvar n) (tapp _ _) = λ ()
isPropNames Γ (dvar n) (tlam _ _) = λ ()
isPropNames Γ (dapp d e) (tvar _) = λ ()
isPropNames Γ (dapp d e) (tapp t u) =
  isProp× (isPropNames Γ d t) (isPropNames Γ e u)
isPropNames Γ (dapp d e) (tlam _ _) = λ ()
isPropNames Γ (dlam d) (tvar _) = λ ()
isPropNames Γ (dlam d) (tapp _ _) = λ ()
isPropNames Γ (dlam d) (tlam x t) = isPropNames (x ∷ Γ) d t

-- At a variable this is `atUniq`, where shadowing does the work.
namesUniq : (Γ : Ctx) (t : RawTm) (d e : DBTm)
  → Names Γ d t → Names Γ e t → d ≡ e
namesUniq Γ (tvar x) (dvar n) (dvar m) a b = cong dvar (atUniq Γ n m x a b)
namesUniq Γ (tvar x) (dvar n) (dapp _ _) a ()
namesUniq Γ (tvar x) (dvar n) (dlam _) a ()
namesUniq Γ (tvar x) (dapp _ _) e () b
namesUniq Γ (tvar x) (dlam _) e () b
namesUniq Γ (tapp t u) (dapp d₁ d₂) (dapp e₁ e₂) a b =
  cong₂ dapp (namesUniq Γ t d₁ e₁ (a .fst) (b .fst))
             (namesUniq Γ u d₂ e₂ (a .snd) (b .snd))
namesUniq Γ (tapp t u) (dapp _ _) (dvar _) a ()
namesUniq Γ (tapp t u) (dapp _ _) (dlam _) a ()
namesUniq Γ (tapp t u) (dvar _) e () b
namesUniq Γ (tapp t u) (dlam _) e () b
namesUniq Γ (tlam x t) (dlam d) (dlam e) a b =
  cong dlam (namesUniq (x ∷ Γ) t d e a b)
namesUniq Γ (tlam x t) (dlam _) (dvar _) a ()
namesUniq Γ (tlam x t) (dlam _) (dapp _ _) a ()
namesUniq Γ (tlam x t) (dvar _) e () b
namesUniq Γ (tlam x t) (dapp _ _) e () b

isPropScope : (Γ : Ctx) (t : RawTm) → isProp (Scope Γ t)
isPropScope Γ t (d , a) (e , b) =
  ΣPathP (q , isProp→PathP (λ i → isPropNames Γ (q i) t) a b)
  where
  q : d ≡ e
  q = namesUniq Γ t d e a b

ScopeSet : Ctx → TheorySet ℓ-zero tm
ScopeSet Γ = Scope Γ , λ t → isProp→isSet (isPropScope Γ t)

rollVar : (Γ : Ctx) (x : Name) → InCtx Γ x → Scope Γ (tvar x)
rollVar Γ x (n , w) = dvar n , w

unrollVar : (Γ : Ctx) (x : Name) → Scope Γ (tvar x) → InCtx Γ x
unrollVar Γ x (dvar n , w) = n , w
unrollVar Γ x (dapp _ _ , ())
unrollVar Γ x (dlam _ , ())

rollApp : (Γ : Ctx) (t u : RawTm)
  → Scope Γ t → Scope Γ u → Scope Γ (tapp t u)
rollApp Γ t u (d , a) (e , b) = dapp d e , (a , b)

unrollFun : (Γ : Ctx) (t u : RawTm) → Scope Γ (tapp t u) → Scope Γ t
unrollFun Γ t u (dapp d e , w) = d , w .fst
unrollFun Γ t u (dvar _ , ())
unrollFun Γ t u (dlam _ , ())

unrollArg : (Γ : Ctx) (t u : RawTm) → Scope Γ (tapp t u) → Scope Γ u
unrollArg Γ t u (dapp d e , w) = e , w .snd
unrollArg Γ t u (dvar _ , ())
unrollArg Γ t u (dlam _ , ())

rollLam : (Γ : Ctx) (x : Name) (t : RawTm)
  → Scope (x ∷ Γ) t → Scope Γ (tlam x t)
rollLam Γ x t (d , w) = dlam d , w

unrollBody : (Γ : Ctx) (x : Name) (t : RawTm)
  → Scope Γ (tlam x t) → Scope (x ∷ Γ) t
unrollBody Γ x t (dlam d , w) = d , w
unrollBody Γ x t (dvar _ , ())
unrollBody Γ x t (dapp _ _ , ())

⊤Set : {s : LSort} → TheorySet ℓ-zero s
⊤Set = ⊤Ty , isSet⊤Ty

-- Trivial binder condition, named so every slot goes through `Ans-ofDec`.
dec⊤ : {s : LSort} → Decidable (⊤Ty {s = s})
dec⊤ _ _ = Sum.inl tt

-- Only `lamOp` uses the dependency on the splitting -- the whole reason for `⊗ᴰ`.
Slots : (o : LOp) → Ctx → NodeArgs ℓ-zero o
Slots varOp Γ ms theVar = InCtxSet Γ
Slots appOp Γ ms a = ScopeSet Γ            -- both slots alike, so no name
Slots lamOp Γ ms theBinder = ⊤Set
Slots lamOp Γ ms theBody = ScopeSet (ms theBinder ∷ Γ)

-- `unrollNode` needs the cell: a term is a node of `o` only where the cover says so.
rollNode : (o : LOp) (Γ : Ctx) → ⊗ᴰ o (Slots o Γ) ⊢ Scope Γ
rollNode varOp Γ m (ms , Eq.refl , ws) = rollVar Γ (ms theVar) (ws theVar)
rollNode appOp Γ m (ms , Eq.refl , ws) =
  rollApp Γ (ms theFun) (ms theArg) (ws theFun) (ws theArg)
rollNode lamOp Γ m (ms , Eq.refl , ws) =
  rollLam Γ (ms theBinder) (ms theBody) (ws theBody)

unrollNode : (o : LOp) (Γ : Ctx) → Scope Γ & NodeAt o ⊢ ⊗ᴰ o (Slots o Γ)
unrollNode varOp Γ m (s , (ms , Eq.refl)) =
  node-mk {ms = ms} λ where theVar → unrollVar Γ (ms theVar) s
unrollNode appOp Γ m (s , (ms , Eq.refl)) =
  node-mk {ms = ms} λ where
    theFun → unrollFun Γ (ms theFun) (ms theArg) s
    theArg → unrollArg Γ (ms theFun) (ms theArg) s
unrollNode lamOp Γ m (s , (ms , Eq.refl)) =
  node-mk {ms = ms} λ where
    theBinder → tt
    theBody → unrollBody Γ (ms theBinder) (ms theBody) s


-- At `LinearAnswer`: the cover commits, so there is nothing to alternate.
module CheckL (𝒯 : LinearAnswer) where

  open Subterm {X = Ctx} isSetCtx (λ _ → 0) hiding (_<_) public
  open LinearCombinators 𝒯 srt order public

  step : Step ScopeSet
  step Γ = look nodeCover branch
    where
    nodeAns : (o : LOp)
      → ▷ (AnsFam ScopeSet) Γ & NodeAt o ⊢ ty (Ans (⊗ᴰSet o (Slots o Γ)))
    nodeAns varOp m (β , (ms , Eq.refl)) =
      Ans-node varOp (preciseλ varOp) {As = Slots varOp Γ} {ms = ms}
        λ where theVar → Ans-ofDec (ms theVar) (decInCtx Γ (ms theVar) tt)
    nodeAns appOp m (β , (ms , Eq.refl)) =
      Ans-node appOp (preciseλ appOp) {As = Slots appOp Γ} {ms = ms}
        λ where
          theFun → callAt Γ
            (callFun {x = Γ} {x' = Γ} (ms theFun) (ms theArg)) β
          theArg → callAt Γ
            (callArg {x = Γ} {x' = Γ} (ms theFun) (ms theArg)) β
    nodeAns lamOp m (β , (ms , Eq.refl)) =
      Ans-node lamOp (preciseλ lamOp) {As = Slots lamOp Γ} {ms = ms}
        λ where
          theBinder → Ans-ofDec (ms theBinder) (dec⊤ (ms theBinder) tt)
          theBody → callAt (ms theBinder ∷ Γ)
            (callBody {x = Γ} {x' = ms theBinder ∷ Γ}
              (ms theBinder) (ms theBody)) β

    branch : (o : LOp)
      → ▷ (AnsFam ScopeSet) Γ & NodeAt o ⊢ ty (Ans (ScopeSet Γ))
    branch o =
      Ans-map& (rollNode o Γ ∘⊢ π₁) (unrollNode o Γ) ∘⊢ (nodeAns o ,& π₂)

  scoped : Checker ScopeSet
  scoped = fix step

module Check (𝒯 : AnswerFunctor) = CheckL (linearOf 𝒯)
