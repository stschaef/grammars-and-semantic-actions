open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
import Theory.Free.Base as FB
open Category
open SortedSig
open SortedEqns
module Theory.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (P : FB.FreePresentation σeq V vs ℓP)
  where

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma.More

open import Cubical.WildCat.LocallySmall.Base

module Pres = FB σeq V vs

private variable ℓA ℓB ℓC : Level

ℓM : Level
ℓM = ℓP

M : MOD σeq ℓM .ob
M = Pres.P P

↓M : S → Type ℓM
↓M s = M .fst s .fst

TheoryTy : (ℓA : Level) → S → Type (ℓ-max ℓM (ℓ-suc ℓA))
TheoryTy ℓA s = ↓M s → Type ℓA

_⊢_ : ∀ {s} → TheoryTy ℓA s → TheoryTy ℓB s → Type (ℓ-max ℓM (ℓ-max ℓA ℓB))
A ⊢ B = ∀ m → A m → B m

infix 1 _⊢_

id⊢ : ∀ {s} {A : TheoryTy ℓA s} → A ⊢ A
id⊢ _ x = x

_∘⊢_ : ∀ {s} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {C : TheoryTy ℓC s}
     → B ⊢ C → A ⊢ B → A ⊢ C
(g ∘⊢ f) m x = g m (f m x)

infixr 9 _∘⊢_

_⋆⊢_ : ∀ {s} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {C : TheoryTy ℓC s}
     → A ⊢ B → B ⊢ C → A ⊢ C
(g ⋆⊢ f) m x = f m (g m x)

infixr 9 _⋆⊢_

open WildCat

-- A locally small wildcat; its `WildCatIso` recovers `StrongEquivalence` on the nose.
THEORYTY : ∀ s →
  WildCat (Σω (Liftω Level) (λ (liftω ℓ) → Liftω (TheoryTy ℓ s))) _
THEORYTY s .Hom[_,_] (_ , liftω A) (_ , liftω B) = A ⊢ B
THEORYTY s .id = id⊢
THEORYTY s ._⋆_ = _⋆⊢_
THEORYTY s .⋆IdL _ = refl
THEORYTY s .⋆IdR _ = refl
THEORYTY s .⋆Assoc _ _ _ = refl

private
  module THEORYTY {s} = WildCatNotation (THEORYTY s)

mkThryTy : ∀ {ℓA} {s} → TheoryTy ℓA s → THEORYTY.Ob
mkThryTy A = _ , liftω A

module _ {s} (A : TheoryTy ℓA s) (B : TheoryTy ℓB s) where
  _≅_ : Type _
  _≅_ = THEORYTY.WildCatIso (mkThryTy A) (mkThryTy B)

⌈_⌉ : ∀ {s} → ↓M s → TheoryTy ℓM s
⌈ a ⌉ m = m Eq.≡ a

⌈gen_⌉ : (v : V) → ↓M (vs v)
⌈gen v ⌉ = Pres.gen P v

-- a generator as a theory type through its representable; notation independent of the theory
literal : (v : V) → TheoryTy ℓM (vs v)
literal v = ⌈ ⌈gen v ⌉ ⌉

＂_＂ : (v : V) → TheoryTy ℓM (vs v)
＂ v ＂ = literal v

infix 30 ＂_＂

interpIn : ∀ {ℓ : Level} → σ .ops → (T : S → Type ℓ) → Type ℓ
interpIn o T = (a : arities σ o) → T (σ .sortOf o a)

op : (o : σ .ops) → interpIn o ↓M → ↓M (σ .resultSort o)
op = M .snd .fst

satStrict : (e : σeq .eqns) (ρ : (w : vars σeq e) → ↓M (σeq .varSort e w))
  → TmRec ↓M op ρ (σeq .lhs e) Eq.≡ TmRec ↓M op ρ (σeq .rhs e)
satStrict = Pres.satStrict P

Val : ∀ {ℓW} {W : Type ℓW} (ws : W → S) → Type _
Val {W = W} ws = (w : W) → ↓M (ws w)

eval : ∀ {ℓW} {W : Type ℓW} {ws : W → S} {s : S} →
  Val ws → Tm σ W ws s → ↓M s
eval ρ N = TmRec ↓M op ρ N
