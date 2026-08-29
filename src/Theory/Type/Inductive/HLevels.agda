{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.More using (_⊔ℓ_)
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

import Theory.Free.Base as FB
module Theory.Type.Inductive.HLevels
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit* ; tt* ; isSetUnit*)
open import Cubical.Data.Empty using (⊥*)
import Cubical.Data.Sum as Sum
open import Cubical.Data.W.Indexed

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.HLevels σeq V vs 𝒫
open import Theory.Type.Inductive.Base σeq V vs 𝒫

private variable ℓA ℓB : Level

isSetValued : ∀ {ℓA ℓX} {X : Type ℓX} {xs : X → S} {s}
  → Functor ℓA X xs s → Type (ℓX ⊔ℓ ℓM ⊔ℓ ℓA)
isSetValued {ℓA = ℓA} {ℓX = ℓX} (k A) = Lift ℓX (isSetTheoryTy A)
isSetValued {ℓA = ℓA} {ℓX = ℓX} (Var x) =
  Lift (ℓX ⊔ℓ ℓM ⊔ℓ ℓA) (Unit* {ℓX ⊔ℓ ℓM ⊔ℓ ℓA})
isSetValued {ℓA = ℓA} {ℓX = ℓX} (⊕e Y F) =
  Lift (ℓM ⊔ℓ ℓA) (isSet Y) × (∀ y → isSetValued (F y))
isSetValued ( &e Y F) = ∀ y → isSetValued (F y)
isSetValued (F &e2 G) = isSetValued F × isSetValued G
isSetValued (⊗e o F) = ∀ a → isSetValued (F a)
isSetValued (⊗ᴰe o F) = ∀ ms a → isSetValued (F ms a)

isSet⟦_⟧ : ∀ {ℓX ℓB} {X : Type ℓX} {xs : X → S} {s}
  (F : Functor ℓA X xs s) → isSetValued F
  → (A : (x : X) → TheoryTy ℓB (xs x))
  → (∀ x → isSetTheoryTy (A x)) → isSetTheoryTy (⟦ F ⟧TheoryTy A)
isSet⟦ k K ⟧ isSetF A isSetA = isSetLiftTheoryTy (isSetF .lower)
isSet⟦ Var x ⟧ isSetF A isSetA = isSetLiftTheoryTy (isSetA x)
isSet⟦ ⊕e Y F ⟧ isSetF A isSetA =
  isSet⊕ᴰ (isSetF .fst .lower) λ y → isSet⟦ F y ⟧ (isSetF .snd y) A isSetA
isSet⟦ &e Y F ⟧ isSetF A isSetA =
  isSet&ᴰ λ y → isSet⟦ F y ⟧ (isSetF y) A isSetA
isSet⟦ F &e2 G ⟧ isSetF A isSetA =
  isSet& (isSet⟦ F ⟧ (isSetF .fst) A isSetA)
    (isSet⟦ G ⟧ (isSetF .snd) A isSetA)
isSet⟦ ⊗e o F ⟧ isSetF A isSetA =
  isSet⊗ᵘ o λ a → isSet⟦ F a ⟧ (isSetF a) A isSetA
isSet⟦ ⊗ᴰe o F ⟧ isSetF A isSetA =
  isSet⊗ᵈ o λ ms a → isSet⟦ F ms a ⟧ (isSetF ms a) A isSetA

module _ {ℓA ℓX} {X : Type ℓX} {xs : X → S} where

  Ix : Type (ℓX ⊔ℓ ℓM)
  Ix = Σ[ x ∈ X ] ↓M (xs x)

  U : (x : X) → TheoryTy ℓ-zero (xs x)
  U x m = Unit*

  FS : ∀ {s} → Functor ℓA X xs s → ↓M s → Type (ℓF ℓA ⊔ℓ ℓX)
  FS F m = ⟦ F ⟧TheoryTy U m

  FP : ∀ {s} (F : Functor ℓA X xs s) (m : ↓M s) → FS F m
    → Type (ℓF ℓA ⊔ℓ ℓX)
  FP (k A) m sh = ⊥*
  FP (Var x) m sh = Unit*
  FP (⊕e Y F) m (y , sh) = FP (F y) m sh
  FP (&e Y F) m sh = Σ[ y ∈ Y ] FP (F y) m (sh y)
  FP (F &e2 G) m (shF , shG) = FP F m shF Sum.⊎ FP G m shG
  FP (⊗e o F) m (ms , e , sh) = Σ[ a ∈ arities σ o ] FP (F a) (ms a) (sh a)
  FP (⊗ᴰe o F) m (ms , e , sh) =
    Σ[ a ∈ arities σ o ] FP (F ms a) (ms a) (sh a)

  next : ∀ {s} (F : Functor ℓA X xs s) (m : ↓M s) (sh : FS F m)
    → FP F m sh → Ix
  next (Var x) m sh p = x , m
  next (⊕e Y F) m (y , sh) p = next (F y) m sh p
  next (&e Y F) m sh (y , p) = next (F y) m (sh y) p
  next (F &e2 G) m (shF , shG) (Sum.inl p) = next F m shF p
  next (F &e2 G) m (shF , shG) (Sum.inr p) = next G m shG p
  next (⊗e o F) m (ms , e , sh) (a , p) = next (F a) (ms a) (sh a) p
  next (⊗ᴰe o F) m (ms , e , sh) (a , p) = next (F ms a) (ms a) (sh a) p

  μIW : (F : (x : X) → Functor ℓA X xs (xs x)) → Ix → Type _
  μIW F = IW
    (λ ix → FS (F (ix .fst)) (ix .snd))
    (λ ix → FP (F (ix .fst)) (ix .snd))
    λ ix → next (F (ix .fst)) (ix .snd)

  isSetFS : ∀ {s} (F : Functor ℓA X xs s) → isSetValued F
    → ∀ m → isSet (FS F m)
  isSetFS F isSetF m = isSet⟦ F ⟧ isSetF U (λ x _ → isSetUnit*) m

  isSetμIW : (F : (x : X) → Functor ℓA X xs (xs x))
    → (∀ x → isSetValued (F x)) → ∀ ix → isSet (μIW F ix)
  isSetμIW F isSetF = isOfHLevelSuc-IW 1 λ ix →
    isSetFS (F (ix .fst)) (isSetF (ix .fst)) (ix .snd)

  getShapeF : ∀ {ℓB s} {A : (x : X) → TheoryTy ℓB (xs x)}
    (F : Functor ℓA X xs s) → ∀ m → ⟦ F ⟧TheoryTy A m → FS F m
  getShapeF F = map F (λ x m z → tt*)

  getSubtreeF : ∀ {ℓB s} (A : (x : X) → TheoryTy ℓB (xs x))
    (F : Functor ℓA X xs s) → ∀ m (x : X)
    → (e : ⟦ F ⟧TheoryTy A m)
    → (p : FP F m (getShapeF F m e))
    → let ix = next F m (getShapeF F m e) p
      in A (ix .fst) (ix .snd)
  getSubtreeF A (k K) m x e ()
  getSubtreeF A (Var x') m x e p = e .lower
  getSubtreeF A (⊕e Y F) m x (y , e) p = getSubtreeF A (F y) m x e p
  getSubtreeF A (&e Y F) m x e (y , p) = getSubtreeF A (F y) m x (e y) p
  getSubtreeF A (F &e2 G) m x (eF , eG) (Sum.inl p) =
    getSubtreeF A F m x eF p
  getSubtreeF A (F &e2 G) m x (eF , eG) (Sum.inr p) =
    getSubtreeF A G m x eG p
  getSubtreeF A (⊗e o F) m x (ms , e , es) (a , p) =
    getSubtreeF A (F a) (ms a) x (es a) p
  getSubtreeF A (⊗ᴰe o F) m x (ms , e , es) (a , p) =
    getSubtreeF A (F ms a) (ms a) x (es a) p

  nodeF : ∀ {ℓB s} (A : (x : X) → TheoryTy ℓB (xs x))
    (F : Functor ℓA X xs s) → ∀ m (x : X)
    → (sh : FS F m)
    → (∀ p → let ix = next F m sh p in A (ix .fst) (ix .snd))
    → ⟦ F ⟧TheoryTy A m
  nodeF A (k K) m x sh subtree = lift (sh .lower)
  nodeF A (Var x') m x sh subtree = lift (subtree tt*)
  nodeF A (⊕e Y F) m x (y , sh) subtree =
    y , nodeF A (F y) m x sh (λ p → subtree p)
  nodeF A (&e Y F) m x sh subtree y =
    nodeF A (F y) m x (sh y) (λ p → subtree (y , p))
  nodeF A (F &e2 G) m x (shF , shG) subtree =
    nodeF A F m x shF (λ p → subtree (Sum.inl p)) ,
    nodeF A G m x shG (λ p → subtree (Sum.inr p))
  nodeF A (⊗e o F) m x (ms , e , sh) subtree =
    ms , e , λ a → nodeF A (F a) (ms a) x (sh a) (λ p → subtree (a , p))
  nodeF A (⊗ᴰe o F) m x (ms , e , sh) subtree =
    ms , e , λ a → nodeF A (F ms a) (ms a) x (sh a) (λ p → subtree (a , p))

  reconstructF : ∀ {ℓB s} (A : (x : X) → TheoryTy ℓB (xs x))
    (F : Functor ℓA X xs s) → ∀ m (x : X) (e : ⟦ F ⟧TheoryTy A m)
    → nodeF A F m x (getShapeF F m e)
        (getSubtreeF A F m x e)
      ≡ e
  reconstructF A (k K) m x e = refl
  reconstructF A (Var x') m x e = refl
  reconstructF A (⊕e Y F) m x (y , e) =
    cong (λ z → y , z) (reconstructF A (F y) m x e)
  reconstructF A (&e Y F) m x e = funExt λ y → reconstructF A (F y) m x (e y)
  reconstructF A (F &e2 G) m x (eF , eG) =
    cong₂ _,_ (reconstructF A F m x eF) (reconstructF A G m x eG)
  reconstructF A (⊗e o F) m x (ms , e , es) =
    cong (λ zs → ms , e , zs) (funExt λ a → reconstructF A (F a) (ms a) x (es a))
  reconstructF A (⊗ᴰe o F) m x (ms , e , es) =
    cong (λ zs → ms , e , zs)
      (funExt λ a → reconstructF A (F ms a) (ms a) x (es a))

  {-# TERMINATING #-}
  encode : (F : (x : X) → Functor ℓA X xs (xs x))
    → ∀ ix → μ F (ix .fst) (ix .snd) → μIW F ix
  encode F (x , m) (roll .m layer) =
    node (getShapeF (F x) m layer) λ p →
      encode F (next (F x) m (getShapeF (F x) m layer) p)
        (getSubtreeF (μ F) (F x) m x layer p)

  decode : (F : (x : X) → Functor ℓA X xs (xs x))
    → ∀ ix → μIW F ix → μ F (ix .fst) (ix .snd)
  decode F (x , m) (node sh subtree) =
    roll m (nodeF (μ F) (F x) m x sh λ p →
      decode F (next (F x) m sh p) (subtree p))

  opaque
    {-# TERMINATING #-}
    isRetract : (F : (x : X) → Functor ℓA X xs (xs x))
      → ∀ x m (z : μ F x m) → decode F (x , m) (encode F (x , m) z) ≡ z
    isRetract F x m (roll .m layer) =
      cong (roll m)
        (cong (nodeF (μ F) (F x) m x _)
          (funExt λ p → isRetract F _ _ _)
        ∙ reconstructF (μ F) (F x) m x layer)

  isSetμ : (F : (x : X) → Functor ℓA X xs (xs x))
    → (∀ x → isSetValued (F x)) → ∀ x → isSetTheoryTy (μ F x)
  isSetμ F isSetF x m =
    isSetRetract (encode F (x , m)) (decode F (x , m)) (isRetract F x m)
      (isSetμIW F isSetF (x , m))
