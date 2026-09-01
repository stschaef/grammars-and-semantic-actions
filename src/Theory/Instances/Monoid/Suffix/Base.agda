{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Proper-suffix order on the free monoid and its guarded eliminations: a
   Löb whose step relation is "proper suffix", `▷⊛r` paid once by `payTok`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Suffix.Base
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; length)
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.FinData using (zero ; suc)
import Cubical.Data.Nat.Order as NO
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt ; tt* ; isSetUnit)
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
open import Cubical.Data.Sum using (isProp⊎)
open import Cubical.Data.Equality.More using (isSet→isSetEq)
import Cubical.Data.Equality as Eq
open import Cubical.Induction.WellFounded
open import Cubical.Relation.Nullary.Base using (Discrete)
import Cubical.Relation.Nullary.Base as NB
open import Cubical.Data.List.Properties using (discreteList)
open import Cubical.Categories.Direct.Base using (WFOrder)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Derivative Alphabet isSetAlphabet
open import Theory.Type.HLevels MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Later.Tag public
open import Theory.Type.Later.Indexed MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Guarded.Base MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Guarded.Justification MonEqns Alphabet (λ _ → tt)
  listPresentation
open import Theory.Instances.Monoid.GuardedSplit MonEqns Alphabet (λ _ → tt)
  listPresentation

private variable ℓA ℓB ℓC ℓD ℓY : Level

-- `w ◂ v`: proper suffix, as data so a memo cell can be located from the witness
_◂_ : String → String → Type ℓM
w ◂ [] = Empty.⊥*
w ◂ (c ∷ v) = (w Eq.≡ v) Sum.⊎ (w ◂ v)

infix 4 _◂_

◂-length : ∀ {w} v → w ◂ v → length w NO.< length v
◂-length (c ∷ v) (Sum.inl Eq.refl) = NO.≤-refl
◂-length (c ∷ v) (Sum.inr i) = NO.<-trans (◂-length v i) NO.≤-refl

◂-irrefl : ∀ w → w ◂ w → Empty.⊥
◂-irrefl w i = NO.¬m<m (◂-length w i)

isProp◂ : ∀ {w} v → isProp (w ◂ v)
isProp◂ [] = Empty.isProp⊥*
isProp◂ {w = w} (c ∷ v) =
  isProp⊎ (isSet→isSetEq (M .fst tt .snd)) (isProp◂ v)
    λ e i → ◂-irrefl v (Eq.transport (_◂ v) e i)

◂-trans : ∀ {u w} v → u ◂ w → w ◂ v → u ◂ v
◂-trans (c ∷ v) i (Sum.inl Eq.refl) = Sum.inr i
◂-trans (c ∷ v) i (Sum.inr j) = Sum.inr (◂-trans v i j)

dec◂ : Discrete Alphabet → ∀ w v → NB.Dec (w ◂ v)
dec◂ dA w [] = NB.no λ z → z .lower
dec◂ dA w (c ∷ v) with discreteList dA w v
... | NB.yes e = NB.yes (Sum.inl (Eq.pathToEq e))
... | NB.no ¬e with dec◂ dA w v
...   | NB.yes i = NB.yes (Sum.inr i)
...   | NB.no ¬i = NB.no (Sum.rec (λ e → ¬e (Eq.eqToPath e)) ¬i)

private
  accStep : ∀ {c} (v : String) → Acc _◂_ v → ∀ u → u ◂ (c ∷ v) → Acc _◂_ u
  accStep v a u (Sum.inl Eq.refl) = a
  accStep v (acc r) u (Sum.inr i) = r u i

  acc◂ : ∀ w → Acc _◂_ w
  acc◂ [] = acc λ u ()
  acc◂ (c ∷ w) = acc (accStep w (acc◂ w))

-- the same order as a bare `WFOrder`, for one component of a lexicographic guard
suffixWFOrder : WFOrder ℓM ℓM
suffixWFOrder = record
  { D = String ; isSetD = M .fst tt .snd ; _<_ = _◂_
  ; isProp< = λ w v → isProp◂ v
  ; trans< = λ {u} {w} {v} → ◂-trans v
  ; wf< = acc◂ }

-- points of the one-nonterminal indexing: a memo row per suffix
SPt : Type ℓM
SPt = IPt {X = Unit} (λ _ → tt)

private
  accPt : ∀ w → Acc _◂_ w → (x : Unit)
    → Acc (λ (p q : SPt) → p .snd ◂ q .snd) (x , w)
  accPt w (acc r) x =
    acc λ q lt → accPt (q .snd) (r (q .snd) lt) (q .fst)

suffixOrder : IPtOrder {X = Unit} (λ _ → tt) ℓM
suffixOrder .IPtOrder.isSetIndex = isSetUnit
suffixOrder .IPtOrder._<_ p q = p .snd ◂ q .snd
suffixOrder .IPtOrder.isProp< p q = isProp◂ (q .snd)
suffixOrder .IPtOrder.trans< {q = q} {r = r} = ◂-trans (r .snd)
suffixOrder .IPtOrder.wf< p = accPt (p .snd) (acc◂ (p .snd)) (p .fst)

-- step relation: a recursive call is entitled to a proper suffix of its input
Below : SPt → SPt → Type ℓM
Below p q = p .snd ◂ q .snd

SFam : (ℓA : Level) → Type _
SFam ℓA = (x : Unit) → TheoryTy ℓA tt

◂-cons : (c : Alphabet) (u w : String) → w ◂ (c ∷ (u ++ w))
◂-cons c [] w = Sum.inl Eq.refl
◂-cons c (d ∷ u) w = Sum.inr (◂-cons d u w)

-- A letter in the left slot puts the right slot strictly below the whole;
-- the only place the suffix order is spent.
◂-lit : (c : Alphabet) {m : String} (ms : interpIn _⊙_ ↓M)
  → op _⊙_ ms Eq.≡ m → literal c (ms zero) → ms (suc zero) ◂ m
◂-lit c ms e lc =
  Eq.transport (ms (suc zero) ◂_) e
    (Eq.transport (λ z → ms (suc zero) ◂ (z ++ ms (suc zero)))
      (Eq.sym lc) (◂-cons c [] (ms (suc zero))))

module Guarded▷ {ℓA} (A : SFam ℓA) (isSetA : ∀ x m → isSet (A x m)) where
  suffixLöb : Löb Below A
  suffixLöb = löbFrom suffixOrder (λ r → r) A isSetA

  open Löb suffixLöb public

  ▷-tok : (c : Alphabet) → Dl c (▷ tt) ⊢ A tt
  ▷-tok c m = app (Sum.inl Eq.refl)

  private
    -- the payment `▷⊛r` asks for is `◂-lit`
    payTok : (c : Alphabet) → PayR suffixLöb {X = literal c}
    payTok c _ = ◂-lit c

  ▷-⊗r : (c : Alphabet) {ℓB : Level} {B : TheoryTy ℓB tt}
    → ▷ tt & (literal c ⊗ B) ⊢ literal c ⊗ (A tt & B)
  ▷-⊗r c = (id⊢ ,⊗ &-swap) ∘⊢ ▷⊛r suffixLöb (payTok c) ∘⊢ &-swap

  ▷-tok⊗ : (c : Alphabet) → ▷ tt & (literal c ⊗ ⊤Ty) ⊢ literal c ⊗ (A tt & ⊤Ty)
  ▷-tok⊗ c = ▷-⊗r c

-- `▷` at this order, on grammars: one nonterminal, so a grammar *is* a
-- family, and nothing downstream names a family or a point.

private
  module G = GuardedIndexed {X = Unit} (λ _ → tt) suffixOrder

  fam : TheorySet ℓA tt → G.SetFam ℓA
  fam A = (λ _ → ty A) , λ _ → A .snd

private variable
  A : TheorySet ℓA tt
  B : TheorySet ℓB tt

-- `▷? ⟨▷⟩` is "at every proper suffix", `▷? ⟨□⟩` is that and here too
▷? : ParserTag → TheorySet ℓA tt → TheorySet (ℓ-max ℓA ℓM) tt
▷? t A = G.▷? t (fam A) .fst tt , G.▷? t (fam A) .snd tt

▷ : TheorySet ℓA tt → TheorySet (ℓ-max ℓA ℓM) tt
▷ = ▷? ⟨▷⟩

□ : TheorySet ℓA tt → TheorySet (ℓ-max ℓA ℓM) tt
□ = ▷? ⟨□⟩

▷map : {t : ParserTag} → ty A ⊢ ty B → ty (▷? t A) ⊢ ty (▷? t B)
▷map {A = A} {B = B} f = G.▷?map {A = fam A} {B = fam B} (λ _ → f) tt

▷lax : {t : ParserTag} → ty (▷? t A) & ty (▷? t B) ⊢ ty (▷? t (A &Set B))
▷lax {A = A} {B = B} = G.▷?lax {A = fam A} {B = fam B} tt

▷laxᴰ : {t : ParserTag} {Y : Type ℓY} (A : Y → TheorySet ℓA tt)
  → &ᴰ Y (λ y → ty (▷? t (A y))) ⊢ ty (▷? t (&ᴰSet A))
▷laxᴰ {t = t} A = G.▷?laxᴰ {t = t} (λ y → fam (A y)) tt

▷next : {t : ParserTag} {D : TheoryTy ℓD tt} → ⊤Ty ⊢ ty A → D ⊢ ty (▷? t A)
▷next {A = A} f = G.▷?next (fam A) (λ _ → f) tt ∘⊢ ⊤Ty-intro

□here : ty (□ A) ⊢ ty A
□here {A = A} = G.□here (fam A) tt

▷wk : {t : ParserTag} → ty (□ A) ⊢ ty (▷? t A)
▷wk {A = A} = G.▷?wk (fam A) tt

▷δ : ty (▷ A) ⊢ ty (▷ (▷ A))
▷δ {A = A} = G.▷δ (fam A) tt

▷δ□ : ty (▷ A) ⊢ ty (▷ (□ A))
▷δ□ = ▷lax ∘⊢ (id⊢ ,& ▷δ)

▷□ : (ty (▷ A) ⊢ ty B) → ty (▷ A) ⊢ ty (□ B)
▷□ {A = A} {B = B} f = G.▷□ {A = fam A} {B = fam B} (λ _ → f) tt

▷⊗r : (c : Alphabet) {C : TheoryTy ℓC tt}
  → ty (▷ A) & (literal c ⊗ C) ⊢ literal c ⊗ (ty A & C)
▷⊗r {A = A} c = Guarded▷.▷-⊗r (fam A .fst) (fam A .snd) c

löbG : (ty (▷ A) ⊢ ty A) → ⊤Ty ⊢ ty A
löbG {A = A} φ = Guarded▷.löb (fam A .fst) (fam A .snd) (λ _ → φ) tt

-- Multi-nonterminal guard: the suffix order with the index rank as tiebreak;
-- a drop-in alternative to `Lex`.

module SufLex {ℓX} {X : Type ℓX} (xs : X → Sorts) (rank : X → ℕ) where
  -- the call took a proper suffix, or stayed put and dropped the rank
  Step : Pt xs → Pt xs → Type ℓM
  Step = Suffix {X = X} {xs = xs} suffixWFOrder (λ _ w → w) rank

  shorter : {y z : X} {v W : String} → v ◂ W → Step (z , v) (y , W)
  shorter = Sum.inl

  dropped : {y z : X} {v : String} → rank z NO.< rank y → Step (z , v) (y , v)
  dropped lt = Sum.inr (refl , lt)

  decStep : Discrete Alphabet → ∀ p q → NB.Dec (Step p q)
  decStep dA = decSuffix {X = X} {xs = xs} suffixWFOrder (λ _ w → w) rank
    (discreteList dA) (dec◂ dA)

  löbBy : isSet X → {ℓR : Level} {R : Pt xs → Pt xs → Type ℓR}
    → (∀ {p q} → R p q → Step p q)
    → (A : IFam xs ℓA) (isSetA : ∀ x m → isSet (A x m)) → Löb R A
  löbBy isSetX = löbBySuffix isSetX suffixWFOrder (λ _ w → w) rank
