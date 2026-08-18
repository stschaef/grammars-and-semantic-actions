{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Cubical.Data.FinData.More where

open import Cubical.Foundations.Prelude
open import Cubical.Data.FinData using (Fin ; zero ; suc)

-- The dependent eliminators for the small arities.  Every slot-indexed family
-- over a binary or ternary operation is built from one of these.
two : ∀ {ℓ} {P : Fin 2 → Type ℓ} → P zero → P (suc zero) → (i : Fin 2) → P i
two a b zero = a
two a b (suc zero) = b

three : ∀ {ℓ} {P : Fin 3 → Type ℓ}
  → P zero → P (suc zero) → P (suc (suc zero)) → (i : Fin 3) → P i
three a b c zero = a
three a b c (suc zero) = b
three a b c (suc (suc zero)) = c
