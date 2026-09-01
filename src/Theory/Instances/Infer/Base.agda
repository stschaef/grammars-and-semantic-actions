{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- Constraint generation and elaboration for untyped lambda terms.  Types are
   `Unify` terms; metavariables are allocated by POSITION over one global
   scope -- `AList` drops scope, so incremental unification is incompatible
   with positional freshness. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
module Theory.Instances.Infer.Base where

open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.List.Properties using (isOfHLevelList)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; isSetℕ ; discreteℕ)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no)
open import Cubical.Relation.Nullary.Properties using (isProp¬)
import Cubical.Data.Sum as Sum
open import Cubical.Data.Sum using (isProp⊎)
import Cubical.Data.Empty as Empty

open import Theory.Instances.Lambda.TermPresentation ℕ isSetℕ
  using (RawTm ; tvar ; tapp ; tlam) public

open import Theory.Instances.Unify.Check public using
  ( Tm ; var ; leaf ; fork ; discreteTm ; isSetTm
  ; Prob ; Stack ; isSetStack
  ; Sol ; isPropSol ; isSetSol ; mgu ; AList ; applyA
  ; Unif ; unifSplit ; applyFork ; mguUnifies ; Unifier )

private variable n m : ℕ

infixr 25 _⇛_
_⇛_ : Tm n → Tm n → Tm n
_⇛_ = fork


Ctx : ℕ → Type ℓ-zero
Ctx n = List (ℕ × Tm n)

isSetCtx : isSet (Ctx n)
isSetCtx = isOfHLevelList 0 (isSetΣ isSetℕ λ _ → isSetTm)

-- By recursion so the cons case holds definitionally (needed by `sound`'s lam case).
mapCtx : (Tm n → Tm m) → Ctx n → Ctx m
mapCtx f [] = []
mapCtx f ((y , B) ∷ Γ) = (y , f B) ∷ mapCtx f Γ

-- Mutually exclusive summands: a proposition, and shadowing resolves inwards.
Lookup : Ctx n → Tm n → ℕ → Type ℓ-zero
Lookup [] A x = Empty.⊥
Lookup ((y , B) ∷ Γ) A x =
  ((x ≡ y) × (A ≡ B)) Sum.⊎ ((x ≡ y → Empty.⊥) × Lookup Γ A x)


isPropLookup : (Γ : Ctx n) (A : Tm n) (x : ℕ) → isProp (Lookup Γ A x)
isPropLookup [] A x = λ ()
isPropLookup ((y , B) ∷ Γ) A x =
  isProp⊎ (isProp× (isSetℕ _ _) (isSetTm _ _))
          (isProp× (isProp¬ _) (isPropLookup Γ A x))
          (λ hit miss → miss .fst (hit .fst))

deBruijn : (Γ : Ctx n) (A : Tm n) (x : ℕ) → Lookup Γ A x → ℕ
deBruijn ((y , B) ∷ Γ) A x (Sum.inl _) = 0
deBruijn ((y , B) ∷ Γ) A x (Sum.inr (_ , v)) = suc (deBruijn Γ A x v)

lookMap : (f : Tm n → Tm m) (Γ : Ctx n) (A : Tm n) (x : ℕ)
  → Lookup Γ A x → Lookup (mapCtx f Γ) (f A) x
lookMap f ((y , B) ∷ Γ) A x (Sum.inl (p , q)) = Sum.inl (p , cong f q)
lookMap f ((y , B) ∷ Γ) A x (Sum.inr (ne , v)) =
  Sum.inr (ne , lookMap f Γ A x v)

-- Total lookup; `lookDef` shows the default is unreachable on a derivation.
hitOr : {ℓp : Level} {P : Type ℓp} → Dec P → Tm n → Tm n → Tm n
hitOr (yes _) B r = B
hitOr (no _) B r = r

lookD : Ctx n → ℕ → Tm n
lookD [] x = leaf
lookD ((y , B) ∷ Γ) x = hitOr (discreteℕ x y) B (lookD Γ x)

lookDef : (Γ : Ctx n) (A : Tm n) (x : ℕ) → Lookup Γ A x → A ≡ lookD Γ x
lookDef ((y , B) ∷ Γ) A x v = go (discreteℕ x y) v
  where
  go : (d : Dec (x ≡ y)) → Lookup ((y , B) ∷ Γ) A x → A ≡ hitOr d B (lookD Γ x)
  go (yes _) (Sum.inl (_ , q)) = q
  go (yes p) (Sum.inr (ne , _)) = Empty.rec (ne p)
  go (no ¬p) (Sum.inl (p , _)) = Empty.rec (¬p p)
  go (no _) (Sum.inr (_ , v)) = lookDef Γ A x v


-- `mvar n k` clamps rather than carrying a bound; soundness does not need
-- the clamp to be unreachable.
mv : RawTm → ℕ
mv (tvar _) = 0
mv (tapp f a) = suc (mv f + mv a)
mv (tlam _ t) = suc (suc (mv t))

fin : (n : ℕ) → ℕ → Fin (suc n)
fin n zero = zero
fin zero (suc k) = zero
fin (suc n) (suc k) = suc (fin n k)

mvar : (n : ℕ) → ℕ → Tm n
mvar zero k = leaf
mvar (suc n) k = var (fin n k)

scopeOf : RawTm → ℕ
scopeOf t = suc (mv t)


-- The typing rules with every equation between types postponed:
--
--   Γ ⊢ x        ⇐ A   ⇝   Γ(x) ≐ A
--   Γ ⊢ f a      ⇐ A   ⇝   [Γ ⊢ f ⇐ βₖ ⇛ A] ++ [Γ ⊢ a ⇐ βₖ]
--   Γ ⊢ λx. t    ⇐ A   ⇝   A ≐ βₖ ⇛ βₖ₊₁ , [Γ,x:βₖ ⊢ t ⇐ βₖ₊₁]
--
gen : (n : ℕ) (Γ : Ctx n) (A : Tm n) (k : ℕ) → RawTm → Stack n
gen n Γ A k (tvar x) = (lookD Γ x , A) ∷ []
gen n Γ A k (tapp f a) =
     gen n Γ (mvar n k ⇛ A) (suc k) f
  ++ gen n Γ (mvar n k) (suc (k + mv f)) a
gen n Γ A k (tlam x t) =
    (A , mvar n k ⇛ mvar n (suc k))
  ∷ gen n ((x , mvar n k) ∷ Γ) (mvar n (suc k)) (suc (suc k)) t


data Core (m : ℕ) : Ctx m → Tm m → Type ℓ-zero where
  cvar : {Γ : Ctx m} {A : Tm m} (x : ℕ) → Lookup Γ A x → Core m Γ A
  capp : {Γ : Ctx m} {A B : Tm m} → Core m Γ (B ⇛ A) → Core m Γ B → Core m Γ A
  clam : {Γ : Ctx m} {A B : Tm m} (x : ℕ) → Core m ((x , B) ∷ Γ) A
       → Core m Γ (B ⇛ A)

erase : {Γ : Ctx m} {A : Tm m} → Core m Γ A → RawTm
erase (cvar x _) = tvar x
erase (capp f a) = tapp (erase f) (erase a)
erase (clam x t) = tlam x (erase t)

eraseSubst : {Γ : Ctx m} {A A' : Tm m} (e : A ≡ A') (c : Core m Γ A)
  → erase (subst (Core m Γ) e c) ≡ erase c
eraseSubst {m = m} {Γ = Γ} e c i = erase (subst-filler (Core m Γ) e c (~ i))


Gen : (n : ℕ) (Γ : Ctx n) (A : Tm n) (k : ℕ) → RawTm → Type ℓ-zero
Gen n Γ A k (tvar x) = Lookup Γ (lookD Γ x) x
Gen n Γ A k (tapp f a) =
    Gen n Γ (mvar n k ⇛ A) (suc k) f
  × Gen n Γ (mvar n k) (suc (k + mv f)) a
Gen n Γ A k (tlam x t) =
  Gen n ((x , mvar n k) ∷ Γ) (mvar n (suc k)) (suc (suc k)) t

isPropGen : (n : ℕ) (Γ : Ctx n) (A : Tm n) (k : ℕ) (t : RawTm)
  → isProp (Gen n Γ A k t)
isPropGen n Γ A k (tvar x) = isPropLookup Γ (lookD Γ x) x
isPropGen n Γ A k (tapp f a) =
  isProp× (isPropGen n Γ (mvar n k ⇛ A) (suc k) f)
          (isPropGen n Γ (mvar n k) (suc (k + mv f)) a)
isPropGen n Γ A k (tlam x t) =
  isPropGen n ((x , mvar n k) ∷ Γ) (mvar n (suc k)) (suc (suc k)) t


-- Instantiated by the front end at `f := applyA (mgu ...)`.
module _ {m : ℕ} (f : Tm n → Tm m)
  (hfork : (a b : Tm n) → f (fork a b) ≡ fork (f a) (f b)) where

  Elab : (Γ : Ctx n) (A : Tm n) → RawTm → Type ℓ-zero
  Elab Γ A t = Σ[ c ∈ Core m (mapCtx f Γ) (f A) ] (erase c ≡ t)

  sound : (Γ : Ctx n) (A : Tm n) (k : ℕ) (t : RawTm)
    → Gen n Γ A k t → Unif f (gen n Γ A k t) → Elab Γ A t
  sound Γ A k (tvar x) d u =
      cvar x (subst (λ z → Lookup (mapCtx f Γ) z x) (u .fst)
                (lookMap f Γ (lookD Γ x) x d))
    , refl
  sound Γ A k (tapp g a) d u = capp gc (ac .fst) , cong₂ tapp ge (ac .snd)
    where
    sp = unifSplit f (gen _ Γ (mvar _ k ⇛ A) (suc k) g)
                     (gen _ Γ (mvar _ k) (suc (k + mv g)) a) u

    gc' = sound Γ (mvar _ k ⇛ A) (suc k) g (d .fst) (sp .fst)
    ac  = sound Γ (mvar _ k) (suc (k + mv g)) a (d .snd) (sp .snd)

    gc : Core m (mapCtx f Γ) (f (mvar _ k) ⇛ f A)
    gc = subst (Core m (mapCtx f Γ)) (hfork (mvar _ k) A) (gc' .fst)

    ge : erase gc ≡ g
    ge = eraseSubst (hfork (mvar _ k) A) (gc' .fst) ∙ gc' .snd
  sound Γ A k (tlam x t) d u =
      subst (Core m (mapCtx f Γ)) shape (clam x (bc .fst))
    , eraseSubst shape (clam x (bc .fst)) ∙ cong (tlam x) (bc .snd)
    where
    bc = sound ((x , mvar _ k) ∷ Γ) (mvar _ (suc k)) (suc (suc k)) t d (u .snd)

    shape : f (mvar _ k) ⇛ f (mvar _ (suc k)) ≡ f A
    shape = sym (u .fst ∙ hfork (mvar _ k) (mvar _ (suc k)))


-- Completeness holds for the shape judgment only; `Agree` suffices because
-- `Gen` reads only the names of a context.
Agree : {n m : ℕ} → Ctx n → Ctx m → Type ℓ-zero
Agree [] [] = Unit
Agree [] (_ ∷ _) = Empty.⊥
Agree (_ ∷ _) [] = Empty.⊥
Agree ((y , _) ∷ Γ) ((y' , _) ∷ Γ') = (y ≡ y') × Agree Γ Γ'

lookAgree : (n m : ℕ) (Γ : Ctx n) (Γ' : Ctx m) → Agree Γ Γ'
  → (A' : Tm m) (x : ℕ) → Lookup Γ' A' x → Lookup Γ (lookD Γ x) x
lookAgree n m [] [] ag A' x ()
lookAgree n m ((y , B) ∷ Γ) ((y' , B') ∷ Γ') (e , ag) A' x v =
  step (discreteℕ x y) v
  where
  step : (d : Dec (x ≡ y)) → Lookup ((y' , B') ∷ Γ') A' x
    → Lookup ((y , B) ∷ Γ) (hitOr d B (lookD Γ x)) x
  step (yes q) _ = Sum.inl (q , refl)
  step (no ¬q) (Sum.inl (p , _)) = Empty.rec (¬q (p ∙ sym e))
  step (no ¬q) (Sum.inr (_ , v')) = Sum.inr (¬q , lookAgree n m Γ Γ' ag A' x v')

genOf : (n : ℕ) {m : ℕ} {Γ' : Ctx m} {A' : Tm m} (c : Core m Γ' A')
  (Γ : Ctx n) → Agree Γ Γ' → (A : Tm n) (k : ℕ) → Gen n Γ A k (erase c)
genOf n (cvar x v) Γ ag A k = lookAgree n _ Γ _ ag _ x v
genOf n (capp f a) Γ ag A k =
    genOf n f Γ ag (mvar n k ⇛ A) (suc k)
  , genOf n a Γ ag (mvar n k) (suc (k + mv (erase f)))
genOf n (clam x c) Γ ag A k =
  genOf n c ((x , mvar n k) ∷ Γ) (refl , ag) (mvar n (suc k)) (suc (suc k))

genComplete : (n : ℕ) (Γ : Ctx n) (A : Tm n) (k : ℕ) (t : RawTm)
  {m : ℕ} {Γ' : Ctx m} {A' : Tm m} (c : Core m Γ' A')
  → Agree Γ Γ' → erase c ≡ t → Gen n Γ A k t
genComplete n Γ A k t c ag e = subst (Gen n Γ A k) e (genOf n c Γ ag A k)


-- No cover with cells `Gen` and `¬ Cor`: its `disjoint` would be
-- `Gen n Γ A k t → Cor Γ t`, refuted at every context by `xx` -- `x x` is
-- well scoped, but no core term erases to it (`Lookup` resolves inwards).
Cor : {n : ℕ} → Ctx n → RawTm → Type ℓ-zero
Cor Γ t = Σ[ m ∈ ℕ ] Σ[ Γ' ∈ Ctx m ] Σ[ A' ∈ Tm m ]
  Σ[ c ∈ Core m Γ' A' ] (Agree Γ Γ' × (erase c ≡ t))

genCell : (n : ℕ) (Γ : Ctx n) (A : Tm n) (k : ℕ) (t : RawTm)
  → Cor Γ t → Gen n Γ A k t
genCell n Γ A k t (m , Γ' , A' , c , ag , e) = genComplete n Γ A k t c ag e
