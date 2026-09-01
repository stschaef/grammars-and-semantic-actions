{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Cover of `Stack n`: "some substitution unifies this stack" vs its
   refutation.  Not circular: the framework hands over `CD.unify n`, a
   decision for `Sol` (machine termination), not solvability -- the cover
   costs exactly `Solvable/complete`, met at `dec-retract`. -}
open import Cubical.Foundations.Prelude
module Theory.Instances.Unify.Cover where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Sum as Sum

open import Theory.Instances.Unify.Check
open import Theory.Instances.Unify.Solvable

open import Theory.Combinator.Complete UEqns ℕ (λ n → n) uPresentation
  using (asCover ; fromCover)

-- solvability as a grammar over the stack theory
-- Neither map of `dec-retract` is free: `solvableOf` is `Correct`'s
-- theorem, `complete` its converse.
decSolvable : (n : ℕ) → Decidable (Solvable n)
decSolvable n = dec-retract (solvableOf n) (complete n) (CD.unify n)

-- `total`: every stack is unified by some substitution or by none.
solvabilityCover : (n : ℕ) → Cover Bool (DecCover (Solvable n))
solvabilityCover n = asCover (decSolvable n)

-- read back, so the identification is used and not merely asserted
solvabilityDecides : (n : ℕ) → Decidable (Solvable n)
solvabilityDecides n = fromCover (solvabilityCover n)


-- Tests are `refl`.  The refuting cell makes the `false`s mean "no
-- substitution unifies this", not "the machine stopped".
private
  x y : Fin 2
  x = zero
  y = suc zero

  solved : Stack 2
  solved = (fork (var x) leaf , fork leaf (var y)) ∷ []

  occurs : Stack 2
  occurs = (var x , fork (var x) leaf) ∷ []

  clash : Stack 2
  clash = (leaf , fork leaf leaf) ∷ []

  verdict : (n : ℕ) → Stack n → Bool
  verdict n ps = isYes (decSolvable n ps tt)

  -- the substitution the affirming cell holds, read one unknown at a time
  witness : (n : ℕ) → Stack n → Fin n → Maybe (Σ[ m ∈ ℕ ] Tm m)
  witness n ps v = Sum.rec (λ s → just (s .fst , s .snd .fst v))
                           (λ _ → nothing) (decSolvable n ps tt)

_ : verdict 2 solved ≡ true
_ = refl

_ : witness 2 solved x ≡ just (0 , leaf)
_ = refl

_ : witness 2 solved y ≡ just (0 , leaf)
_ = refl

_ : verdict 2 occurs ≡ false
_ = refl

_ : verdict 2 clash ≡ false
_ = refl

-- the cover's own reading of the same run, so `total` is exercised
_ : isYes (solvabilityDecides 2 solved tt) ≡ true
_ = refl

_ : isYes (solvabilityDecides 2 occurs tt) ≡ false
_ = refl
