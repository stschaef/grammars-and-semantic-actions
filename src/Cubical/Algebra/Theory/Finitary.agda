-- Finitary multi-sorted algebraic theories
module Cubical.Algebra.Theory.Finitary where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Empty using (⊥*)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Initial
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Displayed.Instances.TotalCategory

private
  variable
    ℓS ℓ ℓ' ℓ'' ℓv ℓX : Level

record SortedSig (S : Type ℓS) ℓ : Type (ℓ-max ℓS (ℓ-suc ℓ)) where
  field
    ops : Type ℓ
    arity : ops → ℕ
    sortOf : (o : ops) → Fin (arity o) → S
    resultSort : ops → S

open SortedSig

arities : {S : Type ℓS} (σ : SortedSig S ℓ) → σ .ops → Type ℓ-zero
arities σ o = Fin (σ .arity o)

module _ {S : Type ℓS} (σ : SortedSig S ℓ) where
  data Tm (V : Type ℓv) (vs : V → S)
    : S → Type (ℓ-max (ℓ-max ℓS ℓ) ℓv) where
    var : (v : V) → Tm V vs (vs v)
    node : (o : σ .ops)
      → ((a : arities σ o) → Tm V vs (σ .sortOf o a))
      → Tm V vs (σ .resultSort o)

module _ {S : Type ℓS} {σ : SortedSig S ℓ} where
  Ops : (S → Type ℓX) → Type _
  Ops X = (o : σ .ops)
    → ((a : arities σ o) → X (σ .sortOf o a)) → X (σ .resultSort o)

  TmRec : (X : S → Type ℓX) (α : Ops X)
    {V : Type ℓv} {vs : V → S} (ρ : (v : V) → X (vs v))
    {s : S} → Tm σ V vs s → X s
  TmRec X α ρ (var v) = ρ v
  TmRec X α ρ (node o ts) = α o (λ a → TmRec X α ρ (ts a))

record SortedEqns {S : Type ℓS} (σ : SortedSig S ℓ) ℓ''
  : Type (ℓ-max (ℓ-max ℓS ℓ) (ℓ-suc ℓ'')) where
  field
    eqns : Type ℓ''
    eqnSort : eqns → S
    varCount : eqns → ℕ
    varSort : (e : eqns) → Fin (varCount e) → S
    lhs rhs : (e : eqns) → Tm σ (Fin (varCount e)) (varSort e) (eqnSort e)

open SortedEqns

vars : {S : Type ℓS} {σ : SortedSig S ℓ} (σeq : SortedEqns σ ℓ'')
     → σeq .eqns → Type ℓ-zero
vars σeq e = Fin (σeq .varCount e)

FAM : (S : Type ℓS) (ℓX : Level)
  → Category (ℓ-max ℓS (ℓ-suc ℓX)) (ℓ-max ℓS ℓX)
FAM S ℓX .Category.ob = S → hSet ℓX
FAM S ℓX .Category.Hom[_,_] X Y = (s : S) → ⟨ X s ⟩ → ⟨ Y s ⟩
FAM S ℓX .Category.id s x = x
FAM S ℓX .Category._⋆_ f g s x = g s (f s x)
FAM S ℓX .Category.⋆IdL f = refl
FAM S ℓX .Category.⋆IdR f = refl
FAM S ℓX .Category.⋆Assoc f g h = refl
FAM S ℓX .Category.isSetHom {y = Y} =
  isSetΠ2 (λ s _ → Y s .snd)

module _ {S : Type ℓS} (σ : SortedSig S ℓ) (ℓX : Level) where
  ALGᴰ : Categoryᴰ (FAM S ℓX) _ _
  ALGᴰ .Categoryᴰ.ob[_] X = Ops {σ = σ} (λ s → ⟨ X s ⟩)
  ALGᴰ .Categoryᴰ.Hom[_][_,_] {x = X} {y = Y} f α β =
    (o : σ .ops) (x : (a : arities σ o) → ⟨ X (σ .sortOf o a) ⟩)
    (y : ⟨ X (σ .resultSort o) ⟩) → y ≡ α o x
    → f (σ .resultSort o) y ≡ β o (λ a → f (σ .sortOf o a) (x a))
  ALGᴰ .Categoryᴰ.idᴰ o x y eq = eq
  ALGᴰ .Categoryᴰ._⋆ᴰ_ {f = f} ϕ ψ o x y eq =
    ψ o (λ a → f (σ .sortOf o a) (x a)) (f (σ .resultSort o) y) (ϕ o x y eq)
  ALGᴰ .Categoryᴰ.⋆IdLᴰ ϕ = refl
  ALGᴰ .Categoryᴰ.⋆IdRᴰ ϕ = refl
  ALGᴰ .Categoryᴰ.⋆Assocᴰ ϕ ψ χ = refl
  ALGᴰ .Categoryᴰ.isSetHomᴰ {y = Y} =
    isSetΠ3 (λ o x y → isSet→ (isProp→isSet (Y _ .snd _ _)))

  ALG : Category _ _
  ALG = ∫C ALGᴰ

module _ {S : Type ℓS} {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'') (ℓX : Level) where

  EQNSᴰ : Categoryᴰ (ALG σ ℓX) _ _
  EQNSᴰ .Categoryᴰ.ob[_] (X , α) =
    (e : σeq .eqns) (ρ : (v : vars σeq e) → ⟨ X (σeq .varSort e v) ⟩)
    → TmRec (λ s → ⟨ X s ⟩) α ρ (σeq .lhs e)
      ≡ TmRec (λ s → ⟨ X s ⟩) α ρ (σeq .rhs e)
  EQNSᴰ .Categoryᴰ.Hom[_][_,_] _ _ _ = Unit* {ℓ-zero}
  EQNSᴰ .Categoryᴰ.idᴰ = tt*
  EQNSᴰ .Categoryᴰ._⋆ᴰ_ _ _ = tt*
  EQNSᴰ .Categoryᴰ.⋆IdLᴰ _ = refl
  EQNSᴰ .Categoryᴰ.⋆IdRᴰ _ = refl
  EQNSᴰ .Categoryᴰ.⋆Assocᴰ _ _ _ = refl
  EQNSᴰ .Categoryᴰ.isSetHomᴰ = isProp→isSet (λ _ _ → refl)

  MODᴰ : Categoryᴰ (FAM S ℓX) _ _
  MODᴰ = ∫Cᴰ (ALGᴰ σ ℓX) EQNSᴰ

  MOD : Category _ _
  MOD = ∫C MODᴰ

  ModHom : (M N : Category.ob MOD) → Type _
  ModHom M N = MOD [ M , N ]
