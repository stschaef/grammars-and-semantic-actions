{- Input generators for the stress suites.

   The point of a stress file is to find where typechecking time turns
   over, so the inputs have to be *generated* rather than pasted: a
   hand-written 128-element cons list pins one size and cannot be moved.
   Every generator here is indexed by its size, so a suite says which
   sizes it asserts and a measurement re-runs it at others. -}
open import Cubical.Foundations.Prelude
module Theory.Instances.Monoid.Stress.Base where

open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Agda.Builtin.String as AS

private variable ℓ : Level

-- `n` copies of one element.
rep : {A : Type ℓ} → ℕ → A → List A
rep zero _ = []
rep (suc n) x = x ∷ rep n x

-- `n` copies of a two-element cycle, so a suite can build a word that is
-- long without being constant.
alternating : {A : Type ℓ} → ℕ → A → A → List A
alternating zero _ _ = []
alternating (suc n) x y = x ∷ alternating n y x

-- `n` copies of a fragment of source text, concatenated.
repText : ℕ → AS.String → AS.String
repText zero _ = ""
repText (suc n) s = AS.primStringAppend s (repText n s)

-- `n` copies wrapped once, which is what a nesting depth needs:
-- `nest 3 "suc " "zero"` is `"suc suc suc zero"`.
nest : ℕ → AS.String → AS.String → AS.String
nest n outer inner = AS.primStringAppend (repText n outer) inner
