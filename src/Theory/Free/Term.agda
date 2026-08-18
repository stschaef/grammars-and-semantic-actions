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
