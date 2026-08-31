open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.SemanticAction.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS} {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'') (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP) where

open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.List using (List ; [] ; _∷_)
import Cubical.Data.List as List
import Cubical.Data.Sum as Sum
import Cubical.Data.Maybe as M

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Top.Base σeq V vs 𝒫
open import Theory.Type.Bottom.Base σeq V vs 𝒫
open import Theory.Type.Sum.Base σeq V vs 𝒫
open import Theory.Type.Sum.Binary.Base σeq V vs 𝒫
open import Theory.Type.Product.Binary.Base σeq V vs 𝒫
open import Theory.Type.Operation.Base σeq V vs 𝒫
open import Theory.Type.Lift.Base σeq V vs 𝒫
open import Theory.Type.Inductive.Base σeq V vs 𝒫
open import Theory.Type.Monad.Maybe σeq V vs 𝒫 using (Maybe)
open import Theory.Type.Decidable.Base σeq V vs 𝒫 using (DecTy)

private variable ℓA ℓB ℓX ℓY : Level

-- Test suites are ordinary external data.  They are independent of the
-- chosen theory; `run` below is the sole boundary at which an internal map
-- out of top is observed.
module Suite where
  Case : Type ℓX → Type ℓX
  Case X = X × X

  infix 6 _↦_
  _↦_ : {W : Type ℓY} {X : Type ℓX} → W → X → W × X
  w ↦ x = w , x

  passes : {X : Type ℓX} → List (Case X) → Type ℓX
  passes cs = List.map fst cs ≡ List.map snd cs

  infix 3 _at_
  _at_ : {W : Type ℓY} {X : Type ℓX}
    → (W → X) → List (W × X) → List (Case X)
  f at cs = List.map (λ c → f (c .fst) ↦ c .snd) cs

open Suite public

Δ : {s : S} → Type ℓX → TheoryTy ℓX s
Δ X = ⊕[ x ∈ X ] ⊤Ty

SemanticAction : {s : S} → TheoryTy ℓA s → Type ℓX → Type _
SemanticAction A X = A ⊢ Δ X

-- Externalisation for every theory and every sort.
run : {s : S} {X : Type ℓX} → (⊤Ty {s = s} ⊢ Δ X) → ↓M s → X
run f m = f m tt .fst

observe : {s : S} {A : TheoryTy ℓA s} {X : Type ℓX}
  → (⊤Ty ⊢ A) → SemanticAction A X → ↓M s → X
observe p a = run (a ∘⊢ p)

semact-pure : {s : S} {A : TheoryTy ℓA s} {X : Type ℓX}
  → X → SemanticAction A X
semact-pure x = σ⊕ x ∘⊢ ⊤Ty-intro

semact-map : {s : S} {A : TheoryTy ℓA s} {X : Type ℓX} {Y : Type ℓY}
  → (X → Y) → SemanticAction A X → SemanticAction A Y
semact-map f x m p = f (x m p .fst) , tt

semact-map-g : {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {X : Type ℓX}
  → A ⊢ B → SemanticAction B X → SemanticAction A X
semact-map-g f x = x ∘⊢ f

semact-Δ : {s : S} {X : Type ℓX} → SemanticAction (Δ {s = s} X) X
semact-Δ = id⊢

semact-⊕ : {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {X : Type ℓX}
  → SemanticAction A X → SemanticAction B X → SemanticAction (A ⊕ B) X
semact-⊕ = ⊕-elim

semact-disjunct : {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  {X : Type ℓX} {Y : Type ℓY}
  → SemanticAction A X → SemanticAction B Y → SemanticAction (A ⊕ B) (X Sum.⊎ Y)
semact-disjunct x y = semact-⊕ (semact-map Sum.inl x) (semact-map Sum.inr y)

-- The internal error case is the external `nothing`.
semact-Maybe : {s : S} {A : TheoryTy ℓA s} {X : Type ℓX}
  → SemanticAction A X → SemanticAction (Maybe A) (M.Maybe X)
semact-Maybe a = semact-⊕ (semact-map M.just a) (semact-pure M.nothing)

-- ...and so is the refutation branch of a decision.
semact-dec : {s : S} {A : TheoryTy ℓA s} {X : Type ℓX}
  → SemanticAction A X → SemanticAction (DecTy A) (M.Maybe X)
semact-dec a = semact-⊕ (semact-map M.just a) (semact-pure M.nothing)

semact-⊕ᴰ : {s : S} {X : Type ℓX} {A : X → TheoryTy ℓA s} {Y : X → Type ℓY}
  → ((x : X) → SemanticAction (A x) (Y x)) → SemanticAction (⊕[ x ∈ X ] A x) (Σ X Y)
semact-⊕ᴰ f = ⊕ᴰ-elim λ x → semact-map (x ,_) (f x)

semact-⊕ᴰ' : {s : S} {X : Type ℓX} {A : X → TheoryTy ℓA s} {Y : Type ℓY}
  → ((x : X) → SemanticAction (A x) Y) → SemanticAction (⊕[ x ∈ X ] A x) Y
semact-⊕ᴰ' = ⊕ᴰ-elim

semact-&-left : {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {X : Type ℓX}
  → SemanticAction A X → SemanticAction (A & B) X
semact-&-left x = x ∘⊢ π₁

semact-&-right : {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {X : Type ℓX}
  → SemanticAction B X → SemanticAction (A & B) X
semact-&-right x = x ∘⊢ π₂

semact-⊥ : {s : S} {X : Type ℓX} → SemanticAction (⊥Ty {s = s}) X
semact-⊥ = ⊥Ty-elim

semact-lift : {s : S} {A : TheoryTy ℓA s} {X : Type ℓX}
  → SemanticAction A X → SemanticAction (LiftTheoryTy ℓB A) X
semact-lift a = a ∘⊢ lowerTy

Δ-⊗ : (o : σ .ops) (X : (a : arities σ o) → Type ℓX)
  → ⊗ᵘ[ o ] (λ a → Δ (X a)) ⊢ Δ ((a : arities σ o) → X a)
Δ-⊗ o X m (ms , e , xs) = (λ a → xs a .fst) , tt

semact-⊗ : (o : σ .ops) {A : interpIn o (TheoryTy ℓA)}
  (X : (a : arities σ o) → Type ℓX)
  → ((a : arities σ o) → SemanticAction (A a) (X a))
  → SemanticAction (⊗ᵘ[ o ] A) ((a : arities σ o) → X a)
semact-⊗ o X f = Δ-⊗ o X ∘⊢ ⊗map o f

-- An action out of an inductive grammar is precisely a Δ-valued algebra.
semact-rec : {ℓX ℓA : Level} {X : Type ℓX} {xs : X → S}
  {F : (x : X) → Functor ℓA X xs (xs x)} {Y : X → Type ℓY}
  → (∀ x → ⟦ F x ⟧TheoryTy (λ x → Δ (Y x)) ⊢ Δ (Y x))
  → (x : X) → SemanticAction (μ F x) (Y x)
semact-rec {F = F} alg x = rec F alg x
