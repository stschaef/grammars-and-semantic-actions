{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Width 3 separates what width 1 cannot:

     S → a b c        S → a b d

   At width 1 both claim `tk ‵a`, so `Predict.altDisjoint` is
   undischargeable (the ascent parser was LC(1)); at width 3 the windows
   are distinct cells, and `branchesSeparate` is a checked term. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Examples.Theory.Combinator.AscentLookahead where

open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Unit using (tt ; tt*)

data Tok : Type where
  ‵a ‵b ‵c ‵d : Tok

_≟T_ : (x y : Tok) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
‵a ≟T ‵a = Sum.inl Eq.refl
‵b ≟T ‵b = Sum.inl Eq.refl
‵c ≟T ‵c = Sum.inl Eq.refl
‵d ≟T ‵d = Sum.inl Eq.refl
‵a ≟T ‵b = Sum.inr λ () ; ‵a ≟T ‵c = Sum.inr λ () ; ‵a ≟T ‵d = Sum.inr λ ()
‵b ≟T ‵a = Sum.inr λ () ; ‵b ≟T ‵c = Sum.inr λ () ; ‵b ≟T ‵d = Sum.inr λ ()
‵c ≟T ‵a = Sum.inr λ () ; ‵c ≟T ‵b = Sum.inr λ () ; ‵c ≟T ‵d = Sum.inr λ ()
‵d ≟T ‵a = Sum.inr λ () ; ‵d ≟T ‵b = Sum.inr λ () ; ‵d ≟T ‵c = Sum.inr λ ()

open import Theory.Instances.Monoid.Combinator.Ascent.Lookahead Tok _≟T_
open import Theory.Instances.Monoid.Combinator.Incomplete.Base Tok _≟T_ ℓ-zero
  using (MaybeAnswer ; MaybeCov)

B0 B1 : TheorySet ℓM tt
B0 = litSet ‵a ⊗Set (litSet ‵b ⊗Set litSet ‵c)
B1 = litSet ‵a ⊗Set (litSet ‵b ⊗Set litSet ‵d)

⊥S : TheorySet ℓM tt
⊥S = LiftTheoryTy ℓM ⊥Ty , isSetLiftTheoryTy isSet⊥Ty

-- window shape matched before letters: `Cw` reduces at a partly-abstract
-- window
cw3 : Tok → Tok → Tok → TheorySet ℓM tt
cw3 ‵a ‵b ‵c = B0
cw3 ‵a ‵b ‵d = B1
cw3 _ _ _ = ⊥S

Cw : Window w3 → TheorySet ℓM tt
Cw ⟨⟩ = ⊥S
Cw (x ◂ ⟨⟩) = ⊥S
Cw (x ◂ y ◂ ⟨⟩) = ⊥S
Cw (x ◂ y ◂ z ◂ ⟨⟩) = cw3 x y z
private
  -- a branch with nothing in it claims any window vacuously
  none3 : (w : Window w3) → ty ⊥S ⊗ ⊤Ty ⊢ Λw w
  none3 w = ⊥Ty-elim ∘⊢ ⊗⊥-annihL ∘⊢ (lowerTy ,⊗ id⊢)

  -- ...and a branch of three literals claims exactly its own window
  full3 : {x y z : Tok}
    → ty (litSet x ⊗Set (litSet y ⊗Set litSet z)) ⊗ ⊤Ty
    ⊢ Λw {w3} (x ◂ y ◂ z ◂ ⟨⟩)
  full3 = (id⊢ ,⊗ (id⊢ ,⊗ (id⊢ ,⊗ liftTy)))
    ∘⊢ (id⊢ ,⊗ ⊗-assoc) ∘⊢ ⊗-assoc

-- third letter concrete in every clause, so `Cw` reduces
leadW : (w : Window w3) → ty (Cw w) ⊗ ⊤Ty ⊢ Λw w
leadW ⟨⟩ = none3 ⟨⟩
leadW (x ◂ ⟨⟩) = none3 (x ◂ ⟨⟩)
leadW (x ◂ y ◂ ⟨⟩) = none3 (x ◂ y ◂ ⟨⟩)
leadW (‵a ◂ ‵b ◂ ‵c ◂ ⟨⟩) = full3
leadW (‵a ◂ ‵b ◂ ‵d ◂ ⟨⟩) = full3
leadW (‵a ◂ ‵b ◂ ‵a ◂ ⟨⟩) = none3 _
leadW (‵a ◂ ‵b ◂ ‵b ◂ ⟨⟩) = none3 _
leadW (‵a ◂ ‵c ◂ z ◂ ⟨⟩) = none3 _
leadW (‵a ◂ ‵d ◂ z ◂ ⟨⟩) = none3 _
leadW (‵a ◂ ‵a ◂ z ◂ ⟨⟩) = none3 _
leadW (‵b ◂ y ◂ z ◂ ⟨⟩) = none3 _
leadW (‵c ◂ y ◂ z ◂ ⟨⟩) = none3 _
leadW (‵d ◂ y ◂ z ◂ ⟨⟩) = none3 _

-- the ascent parser's choice, at width 3
module W3 = WidthPredict MaybeAnswer MaybeCov εSet w3 Cw leadW

-- THE POINT: separation from the width-3 cover; at width 1 both branches
-- claim `tk ‵a` and no such term exists
branchesSeparate : ty B0 & ty B1 ⊢ ⊥Ty
branchesSeparate =
  W3.altDisjoint (‵a ◂ ‵b ◂ ‵c ◂ ⟨⟩) (‵a ◂ ‵b ◂ ‵d ◂ ⟨⟩) (λ ())
