-- Free model on a signature (i.e. a theory without equations)
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
open import Cubical.Data.Empty using (⊥)
module Theory.Free.Term
  {ℓ ℓ'' ℓv ℓS} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (noEqns : σeq .eqns → ⊥)
  (isSetS : isSet S) (isSetV : isSet V) (isSetOps : isSet (σ .ops))
  where

import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr ; isSet⊎)
import Cubical.Data.Equality as Eq
open import Cubical.Data.Equality.More using (isSet→isSetEq)
open import Cubical.Data.W.Indexed using (IW ; node ; isOfHLevelSuc-IW)

open import Theory.Free.Base σeq V vs

private variable ℓX : Level

ℓTerm : Level
ℓTerm = ℓ-max ℓS (ℓ-max ℓv ℓ)

private
  Shape : S → Type ℓTerm
  Shape s = (Σ[ v ∈ V ] (vs v Eq.≡ s)) ⊎ (Σ[ o ∈ σ .ops ] (σ .resultSort o Eq.≡ s))

  Pos : (s : S) → Shape s → Type ℓ-zero
  Pos s (inl _) = ⊥
  Pos s (inr (o , _)) = arities σ o

  sortAt : (s : S) (sh : Shape s) → Pos s sh → S
  sortAt s (inr (o , _)) a = σ .sortOf o a

  isSetShape : (s : S) → isSet (Shape s)
  isSetShape s = isSet⊎
    (isSetΣ isSetV λ _ → isProp→isSet (isSet→isSetEq isSetS))
    (isSetΣ isSetOps λ _ → isProp→isSet (isSet→isSetEq isSetS))

Term : S → Type ℓTerm
Term = IW Shape Pos sortAt

private
  isSetTerm : (s : S) → isSet (Term s)
  isSetTerm = isOfHLevelSuc-IW 1 isSetShape

  termOps : Ops {σ = σ} Term
  termOps o ms = node (inr (o , Eq.refl)) ms

  termSat : (e : σeq .eqns)
    (ρ : (w : vars σeq e) → Term (σeq .varSort e w))
    → TmRec Term termOps ρ (σeq .lhs e) ≡ TmRec Term termOps ρ (σeq .rhs e)
  termSat e ρ = Empty.rec (noEqns e)

  TermModel : MOD σeq ℓTerm .ob
  TermModel = (λ s → Term s , isSetTerm s) , termOps , termSat

fold : {X : S → Type ℓX} (α : Ops {σ = σ} X) (ρ : (v : V) → X (vs v))
  → {s : S} → Term s → X s
fold {X = X} α ρ (node (inl (v , Eq.refl)) _) = ρ v
fold {X = X} α ρ (node (inr (o , Eq.refl)) sub) =
  α o (λ a → fold {X = X} α ρ (sub a))

private
  foldUniq : {X : S → Type ℓX} (α : Ops {σ = σ} X) (ρ : (v : V) → X (vs v))
    (f : (s : S) → Term s → X s)
    → ((o : σ .ops) (ms : (a : arities σ o) → Term (σ .sortOf o a))
        → f (σ .resultSort o) (termOps o ms)
          ≡ α o (λ a → f (σ .sortOf o a) (ms a)))
    → ((v : V) → f (vs v) (node (inl (v , Eq.refl)) (λ ())) ≡ ρ v)
    → {s : S} (m : Term s) → f s m ≡ fold α ρ m
  foldUniq {X = X} α ρ f homf fβ (node (inl (v , Eq.refl)) sub) =
    cong (λ z → f (vs v) (node (inl (v , Eq.refl)) z)) (funExt (λ ())) ∙ fβ v
  foldUniq {X = X} α ρ f homf fβ (node (inr (o , Eq.refl)) sub) =
      homf o sub
    ∙ cong (α o) (funExt λ a → foldUniq {X = X} α ρ f homf fβ (sub a))

termPresentation : FreePresentation ℓTerm
termPresentation .P = TermModel
termPresentation .gen v = node (inl (v , Eq.refl)) (λ ())
termPresentation .satStrict e ρ = Empty.rec (noEqns e)
termPresentation .rec isSetX α sat ρ = fold α ρ
termPresentation .recGen isSetX α sat ρ v = refl
termPresentation .recOp isSetX α sat ρ o ms = refl
termPresentation .recUniq isSetX α sat ρ f homf fβ m = foldUniq α ρ f homf fβ m

genT : (v : V) → Term (vs v)
genT v = node (inl (v , Eq.refl)) (λ ())

opT : (o : σ .ops) → ((a : arities σ o) → Term (σ .sortOf o a))
    → Term (σ .resultSort o)
opT = termOps

data TermView : {s : S} → Term s → Type ℓTerm where
  isGen : (v : V) → TermView (genT v)
  isOp  : (o : σ .ops) (ms : (a : arities σ o) → Term (σ .sortOf o a))
        → TermView (opT o ms)

termView : {s : S} (t : Term s) → TermView t
termView (node (inl (v , Eq.refl)) sub) = out
  where
  -- a generator's child tuple is empty, so it *is* `genT v`
  noKids : (λ ()) ≡ sub
  noKids = funExt λ ()

  out : TermView (node (inl (v , Eq.refl)) sub)
  out = subst (λ z → TermView (node (inl (v , Eq.refl)) z)) noKids (isGen v)
termView (node (inr (o , Eq.refl)) sub) = isOp o sub

elimTerm : {ℓP : Level} {P : {s : S} → Term s → Type ℓP}
  → ((v : V) → P (genT v))
  → ((o : σ .ops) (ms : (a : arities σ o) → Term (σ .sortOf o a))
      → ((a : arities σ o) → P (ms a)) → P (opT o ms))
  → {s : S} (t : Term s) → P t
elimTerm {P = P} pg po (node (inl (v , Eq.refl)) sub) =
  subst (λ z → P (node (inl (v , Eq.refl)) z)) (funExt λ ()) (pg v)
elimTerm {P = P} pg po (node (inr (o , Eq.refl)) sub) =
  po o sub λ a → elimTerm {P = P} pg po (sub a)


-- What a free term presentation gives a combinator framework.
--
-- `Theory/Combinator/Core` asks a signature for two things: that each
-- operation decompose uniquely (`Precise`), so that a refutation at one
-- slot refutes the node; and a well-founded order for the guard.  A free
-- term algebra has both, for *every* operation, and neither depends on the
-- signature -- so a checker over any such theory gets them here rather than
-- re-proving them.  (The free monoid has neither: a word splits many ways,
-- which is why that development has token rules and a suffix order.)

open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-assoc ; +-comm ; +-suc)
import Cubical.Data.Nat.Order as NO
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)

private
  shOf : {s : S} → Term s → Shape s
  shOf (node sh _) = sh

  kidsOf : {s : S} (t : Term s)
    → (p : Pos s (shOf t)) → Term (sortAt s (shOf t) p)
  kidsOf (node sh f) = f

-- `opT o` is an embedding: the node determines its arguments.
opT-inj : (o : σ .ops) {ms ms' : (a : arities σ o) → Term (σ .sortOf o a)}
  → opT o ms ≡ opT o ms' → ms ≡ ms'
opT-inj o {ms = ms} {ms' = ms'} q =
  subst Motive (isSetShape _ _ _ (λ i → shOf (q i)) refl) (λ i → kidsOf (q i))
  where
  Motive : shOf (opT o ms) ≡ shOf (opT o ms) → Type ℓTerm
  Motive r = PathP (λ i → (p : Pos _ (r i)) → Term (sortAt _ (r i) p)) ms ms'

-- ...which is exactly `Precise o`, stated where `Core` can use it.
preciseTerm : (o : σ .ops) (m : Term (σ .resultSort o))
  → isProp (Σ[ ms ∈ ((a : arities σ o) → Term (σ .sortOf o a)) ] (opT o ms Eq.≡ m))
preciseTerm o m (ms , e) (ms' , e') =
  ΣPathP ( opT-inj o (Eq.eqToPath e ∙ sym (Eq.eqToPath e'))
         , isProp→PathP (λ _ → isSet→isSetEq (isSetTerm _)) e e' )

-- The head operation, for the no-confusion a checker needs when it refutes
-- the branches it did not take.  The signature's own discrimination of
-- operations is the instance's job; this reduces it to that.
headOpT : {s : S} → Term s → Maybe (σ .ops)
headOpT (node (inl _) _) = nothing
headOpT (node (inr (o , _)) _) = just o

headOpT-node : (o : σ .ops) (ms : (a : arities σ o) → Term (σ .sortOf o a))
  → headOpT (opT o ms) ≡ just o
headOpT-node o ms = refl

-- The measure the guard descends on: a term's size.  Every argument of a
-- node is strictly smaller, which is the whole descent obligation.
private
  sumFin : {n : ℕ} → (Fin n → ℕ) → ℕ
  sumFin {zero} f = 0
  sumFin {suc n} f = f zero + sumFin (λ i → f (suc i))

  sumFin-≥ : {n : ℕ} (f : Fin n → ℕ) (i : Fin n) → f i NO.≤ sumFin f
  sumFin-≥ {suc n} f zero = sumFin (λ j → f (suc j)) , +-comm _ (f zero)
  sumFin-≥ {suc n} f (suc i) =
    (f zero + sumFin-≥ (λ k → f (suc k)) i .fst)
    , ( sym (+-assoc (f zero) (sumFin-≥ (λ k → f (suc k)) i .fst) (f (suc i)))
      ∙ cong (f zero +_) (sumFin-≥ (λ k → f (suc k)) i .snd) )

termSize : {s : S} → Term s → ℕ
termSize (node (inl _) _) = 1
termSize (node (inr (o , Eq.refl)) sub) = suc (sumFin λ a → termSize (sub a))

argSize< : (o : σ .ops) (ms : (a : arities σ o) → Term (σ .sortOf o a))
  (a : arities σ o) → termSize (ms a) NO.< termSize (opT o ms)
argSize< o ms a = sumFin-≥ (λ b → termSize (ms b)) a .fst
  , (+-suc (sumFin-≥ (λ b → termSize (ms b)) a .fst) (termSize (ms a))
     ∙ cong suc (sumFin-≥ (λ b → termSize (ms b)) a .snd))
