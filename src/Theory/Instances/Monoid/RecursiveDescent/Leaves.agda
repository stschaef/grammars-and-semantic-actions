{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- What a parser result says about the residual.  A result is already
   tagged by the suffix it left, so "succeeded leaving exactly `r`" is a
   point of `⌈ r ⌉` and failure is `⊥Ty` -- a grammar, not a predicate on
   the value.  Recording the residual rather than the consumed prefix is
   what lets sequencing compose without appealing to `++`-associativity. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.RecursiveDescent.Leaves
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)) where

open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.List using ([] ; _∷_)
open import Cubical.Data.Unit using (tt ; tt*)
open import Cubical.Data.Sigma using (_,_)

-- not re-exported: consumers already have these from their grammar layer, and
-- binding them twice makes every name ambiguous
open import Theory.Instances.Monoid.RecursiveDescent.List Alphabet _≟_

private variable ℓ ℓ' : Level

Leaves : {A : TheoryTy ℓ tt} {w : ↓M tt}
  → Maybe (A ⊗ ⊤Ty) w → TheoryTy ℓM tt
Leaves (Sum.inl (ms , _ , _)) = ⌈ ms (suc zero) ⌉
Leaves (Sum.inr _) = LiftTheoryTy ℓM ⊥Ty

-- the same read as a grammar in the input: the codomain of every
-- correctness statement about a parser
LeavesAt : {A : TheoryTy ℓ tt} → Parser A → ↓M tt → TheoryTy ℓM tt
LeavesAt p r w = Leaves (p w tt) r

-- along an equation of inputs, by matching rather than by `subst`
castLeaves : {A : TheoryTy ℓ tt} (p : Parser A) (r : ↓M tt) {u v : ↓M tt}
  → u Eq.≡ v → LeavesAt p r u → LeavesAt p r v
castLeaves _ _ Eq.refl h = h

-- relabelling the tree leaves the residual alone
leaves-map : {A : TheoryTy ℓ tt} {B : TheoryTy ℓ' tt} (f : A ⊢ B)
  {w : ↓M tt} (res : Maybe (A ⊗ ⊤Ty) w)
  → Leaves res ⊢ Leaves (Monad.fmap MaybeMonad (f ,⊗ id⊢) w res)
leaves-map f (Sum.inl _) = id⊢
leaves-map f (Sum.inr _) = id⊢

-- Sequencing hands the second parser's residual straight out.  The inner
-- `Maybe` is matched through the pair, not by `with`: a `with` does not
-- reach inside `⊗map`, so `Maybe⊗r` stays stuck.
leaves-⊗r : {A : TheoryTy ℓ tt} {B : TheoryTy ℓ' tt} {w : ↓M tt}
  (v : (A ⊗ Maybe (B ⊗ ⊤Ty)) w)
  → Leaves (v .snd .snd .snd .fst)
  ⊢ Leaves (Monad.fmap MaybeMonad ⊗-assoc⁻ w (Maybe⊗r w v))
leaves-⊗r (_ , _ , (_ , (Sum.inl _ , _))) = id⊢
leaves-⊗r (_ , _ , (_ , (Sum.inr _ , _))) = id⊢

-- the first parser's residual is matched, not substituted along
leaves-seqP : {A : TheoryTy ℓ tt} {B : TheoryTy ℓ' tt} (q : Parser B)
  {w : ↓M tt} (res : Maybe (A ⊗ ⊤Ty) w) (r₁ r₂ : ↓M tt)
  → Leaves res r₁ → Leaves (q r₁ tt) r₂
  → Leaves (onSuccess
      (Monad.fmap MaybeMonad ⊗-assoc⁻ ∘⊢ Maybe⊗r ∘⊢ (id⊢ ,⊗ q)) w res) r₂
leaves-seqP q (Sum.inr _) _ _ fails _ = Empty.rec* (fails .lower)
leaves-seqP q {w = w} (Sum.inl (ms , e , xs)) _ r₂ Eq.refl hq =
  leaves-⊗r ((id⊢ ,⊗ q) w (ms , e , xs)) r₂ hq

-- Reading the letter that is there leaves the rest.  The two letters are
-- kept apart so `Eq.refl` has something to unify: without K, matching on
-- `c Eq.≡ c` at an abstract `c` is stuck.
litP-ok : (c d : Alphabet) (r : ↓M tt) → c Eq.≡ d
  → Leaves (litP c (d ∷ r) tt) r
-- The decision is taken at the fibre, and by a named branch rather than by
-- `with`: the module abstracts over a level, so a `with` here would generate
-- a `Typeω` function.  `lookStep` is already a function of the decision, so
-- naming it is all that is needed to make the goal reduce.
litP-ok c d r p = go (tk d ≟M tk c)
  where
  go : (w : (tk d Eq.≡ tk c) Sum.⊎ ((tk d Eq.≡ tk c) → Empty.⊥))
     → Leaves (lookCase (tk c) (tk d) w (d ∷ r)
         (two (d ∷ []) r , Eq.refl , Eq.refl , tt , tt*)) r
  go (Sum.inl Eq.refl) = Eq.refl
  go (Sum.inr ne) = Empty.rec (ne (Eq.ap tk (Eq.sym p)))
