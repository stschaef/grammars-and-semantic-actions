{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- One regular expression, compiled once, run at all three answers.

   `amb` is `(a ∣ aa)*`, the standard ambiguous regex: the number of ways to
   chop `aⁿ` into ones and twos is `Fib (n+1)`.  The three answers show
   exactly what each one throws away.  `SDec.regex`, `SInc.regex` and
   `SND.regex` are the same `⟦_⟧P` at three `AnswerFunctor`s -- the compiler
   is written once, in `Combinator/Syntax`. -}
open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.Combinator.Grammars.RegexTests where

open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (_,_)
import Cubical.Data.Sum as Sum
import Cubical.Data.Maybe as M
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

data Two : Type ℓ-zero where
  a b : Two

_≟_ : (x y : Two) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
_≟_ a a = Sum.inl Eq.refl
_≟_ b b = Sum.inl Eq.refl
_≟_ a b = Sum.inr λ ()
_≟_ b a = Sum.inr λ ()

import Theory.Instances.Monoid.Combinator.Decidable.Base
  Two _≟_ ℓ-zero as Dec
import Theory.Instances.Monoid.Combinator.Incomplete.Base
  Two _≟_ ℓ-zero as Inc
import Theory.Instances.Monoid.Combinator.NonDet.Base
  Two _≟_ ℓ-zero as ND

open import Theory.Instances.Monoid.Combinator.Grammars.Regex Two _≟_

import Theory.Instances.Monoid.Combinator.Syntax
  Two _≟_ Dec.DecAnswer as SDec
import Theory.Instances.Monoid.Combinator.Syntax
  Two _≟_ Inc.MaybeAnswer as SInc
import Theory.Instances.Monoid.Combinator.Syntax
  Two _≟_ ND.NDAnswer as SND

open Dec using (_↦_ ; _at_ ; passes ; String ; ⟨▷⟩ ; ⟨□⟩)

ab : Reg ⟨▷⟩
ab = ＂ a ＂r ⊗r ＂ b ＂r

amb : Reg ⟨□⟩
amb = (＂ a ＂r ⊕r (＂ a ＂r ⊗r ＂ a ＂r)) *r

decAmb : String → M.Maybe (Tree amb)
decAmb = Dec.observe (SDec.regex amb) (Dec.semact-dec (regAct amb))

incAmb : String → M.Maybe (Tree amb)
incAmb = Inc.observe (SInc.regex amb) (Inc.semact-Maybe (regAct amb))

ndAmb : String → List (Tree amb)
ndAmb = ND.observe (SND.regex amb) (ND.semact-ND (regAct amb))

decAb : String → M.Maybe (Tree ab)
decAb = Dec.observe (SDec.regex ab) (Dec.semact-dec (regAct ab))

ndAb : String → List (Tree ab)
ndAb = ND.observe (SND.regex ab) (ND.semact-ND (regAct ab))

-- `ab` is unambiguous, so the answers agree up to `just`/singleton.

ab-dec : passes
  (decAb at
    ( (a ∷ b ∷ [])     ↦ M.just (a , b)
    ∷ (a ∷ [])         ↦ M.nothing
    ∷ (a ∷ b ∷ b ∷ []) ↦ M.nothing
    ∷ [] ))
ab-dec = refl

ab-nd : passes
  (ndAb at
    ( (a ∷ b ∷ [])     ↦ ((a , b) ∷ [])
    ∷ (a ∷ [])         ↦ []
    ∷ (a ∷ b ∷ b ∷ []) ↦ []
    ∷ [] ))
ab-nd = refl

-- `amb` is where they part.  Both `Dec` and `Maybe` return one chop and
-- discard the rest; `ND` returns the whole `Fib (n+1)` fan.

amb-count : passes
  ((λ w → length (ndAmb w)) at
    ( []                         ↦ 1
    ∷ (a ∷ [])                   ↦ 1
    ∷ (a ∷ a ∷ [])               ↦ 2
    ∷ (a ∷ a ∷ a ∷ [])           ↦ 3
    ∷ (a ∷ a ∷ a ∷ a ∷ [])       ↦ 5
    ∷ (a ∷ b ∷ [])               ↦ 0
    ∷ [] ))
amb-count = refl

amb-nd : passes
  (ndAmb at
    ( (a ∷ a ∷ a ∷ []) ↦
        ( (Sum.inl a ∷ Sum.inl a ∷ Sum.inl a ∷ [])
        ∷ (Sum.inl a ∷ Sum.inr (a , a) ∷ [])
        ∷ (Sum.inr (a , a) ∷ Sum.inl a ∷ [])
        ∷ [] )
    ∷ [] ))
amb-nd = refl

amb-dec : passes
  (decAmb at
    ( (a ∷ a ∷ a ∷ []) ↦ M.just (Sum.inl a ∷ Sum.inl a ∷ Sum.inl a ∷ [])
    ∷ (a ∷ b ∷ [])     ↦ M.nothing
    ∷ [] ))
amb-dec = refl

amb-inc : passes
  (incAmb at
    ( (a ∷ a ∷ a ∷ []) ↦ M.just (Sum.inl a ∷ Sum.inl a ∷ Sum.inl a ∷ [])
    ∷ (a ∷ b ∷ [])     ↦ M.nothing
    ∷ [] ))
amb-inc = refl
