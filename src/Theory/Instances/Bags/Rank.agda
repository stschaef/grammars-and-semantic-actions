{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Equality as Eq
import Cubical.Algebra.Theory.Finitary.Free.Closing as Cl
open SortedSig
open SortedEqns
module Theory.Instances.Bags.Rank (El : Type ℓ-zero) where

open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; isSetℕ ; +-assoc
  ; +-comm ; +-zero ; +-suc)
open import Cubical.Data.Nat.Order.Recursive renaming (_<_ to _<ℕ_) using ()
open import Cubical.Data.Nat.WFOrder using (ℕWFRec)
import Cubical.Data.Nat.Order.Recursive as R
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt ; tt* ; isSetUnit)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Bags.Base El
open import Theory.Type.Guarded.Base BagEqns El (λ _ → tt) closingPresentation
open import Theory.Instances.Monoid.GuardedSplit BagEqns El (λ _ → tt)
  closingPresentation
open import Theory.Type.Guarded.Justification BagEqns El (λ _ → tt)
  closingPresentation

private
  N : Sorts → Type ℓ-zero
  N _ = ℕ

  +Ops : Ops {σ = MonSig} N
  +Ops ε· f = zero
  +Ops _⊙_ f = f zero + f (suc zero)

  +Sat : (e : BagEqns .eqns)
         (ρ : (w : vars BagEqns e) → N (BagEqns .varSort e w))
       → TmRec N +Ops ρ (BagEqns .lhs e) ≡ TmRec N +Ops ρ (BagEqns .rhs e)
  +Sat (mon assoc) ρ = sym (+-assoc (ρ zero) (ρ (suc zero)) (ρ (suc (suc zero))))
  +Sat (mon unitL) ρ = refl
  +Sat (mon unitR) ρ = +-zero (ρ zero)
  +Sat (ext comm) ρ = +-comm (ρ zero) (ρ (suc zero))

size : Bag → ℕ
size m = Cl.rec BagEqns (λ _ → isSetℕ) +Ops +Sat (λ _ → 1) m

Fam : (ℓA : Level) → Type _
Fam ℓA = (s : Sorts) → TheoryTy ℓA s

-- the step relation: the only place `size` appears in a type
_◃_ : Pt {X = Sorts} (λ s → s) → Pt (λ s → s) → Type ℓ-zero
p ◃ q = size (p .snd) <ℕ size (q .snd)

private
  -- the recursive order: both bounds are structural, with no transport
  ltLeft : (a b : ℕ) → a <ℕ suc (a + b)
  ltLeft zero b = _
  ltLeft (suc a) b = ltLeft a b

  ≤-suc : (a b : ℕ) → a R.≤ b → a R.≤ suc b
  ≤-suc zero b p = _
  ≤-suc (suc a) (suc b) p = ≤-suc a b p

  ltRight : (a b : ℕ) → b <ℕ suc (a + b)
  ltRight zero b = R.≤-refl b
  ltRight (suc a) b = ≤-suc b (a + b) (ltRight a b)

  oneDrop : {m n : Bag} → size m ≡ suc (size n) → (tt , n) ◃ (tt , m)
  oneDrop {n = n} sz = subst (size n <ℕ_) (sym sz) (R.≤-refl (size n))

  bothDrop : {m b c : Bag} → size m ≡ suc (size b + size c)
    → ((tt , b) ◃ (tt , m)) × ((tt , c) ◃ (tt , m))
  bothDrop {b = b} {c = c} sz =
      subst (size b <ℕ_) (sym sz) (ltLeft (size b) (size c))
    , subst (size c <ℕ_) (sym sz) (ltRight (size b) (size c))
-- Divide-and-conquer termination, once and for all: peeling a generator drops the rank by one.
module Guarded▷ {ℓA} (A : Fam ℓA) (isSetA : ∀ s m → isSet (A s m)) where
  private
    bagLöb : Löb _◃_ A
    bagLöb = löbByMeasure {X = Sorts} {xs = λ s → s}
      isSetUnit ℕWFRec (λ p → size (p .snd)) (λ r → r) A isSetA

  open Löb bagLöb public

  private
    -- Stated at `m` itself, never `op _⊙_ ms`, so `app` applies with no transport.
    -- Proofs, not terms: they relate the point `ms a` to `m`, and a `⊢`-map preserves its index.
    genDrop : (y : El) (m : Bag) (ms : interpIn _⊙_ ↓M) → op _⊙_ ms Eq.≡ m
      → ⌈ ⌈gen y ⌉ ⌉ (ms zero) → size m ≡ suc (size (ms (suc zero)))
    genDrop y m ms e hd =
      sym (cong size (Eq.eqToPath e))
      ∙ cong (_+ size (ms (suc zero))) (cong size (Eq.eqToPath hd))

    payCons : (y : El) → PayR bagLöb {X = ⌈ ⌈gen y ⌉ ⌉}
    payCons y m ms e hd = oneDrop (genDrop y m ms e hd)

    paySplit : (y : El) → PayR² bagLöb {X = ⌈ ⌈gen y ⌉ ⌉}
    paySplit y m ms ns e e' hd =
      bothDrop (genDrop y m ms e hd ∙ cong suc (sym (cong size (Eq.eqToPath e'))))

  -- peeling a generator: the cofactor is one shorter
  ▷-cons : ∀ {ℓB} (y : El) {B : TheoryTy ℓB tt}
    → (⌈ ⌈gen y ⌉ ⌉ ⊎B B) & ▷ tt ⊢ ⌈ ⌈gen y ⌉ ⌉ ⊎B (B & A tt)
  ▷-cons y = ▷⊛r bagLöb (payCons y)

  -- ... and splitting what the generator left: both halves are below it
  ▷-split : ∀ {ℓB} (y : El) {B C : TheoryTy ℓB tt}
    → (⌈ ⌈gen y ⌉ ⌉ ⊎B (B ⊎B C)) & ▷ tt
    ⊢ ⌈ ⌈gen y ⌉ ⌉ ⊎B ((B & A tt) ⊎B (C & A tt))
  ▷-split y = ▷⊛r² bagLöb (paySplit y)
