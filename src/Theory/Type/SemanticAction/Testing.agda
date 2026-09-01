-- Test-suite plumbing: external data, independent of any theory.
module Theory.Type.SemanticAction.Testing where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.List using (List)
import Cubical.Data.List as List

private variable ℓX ℓY : Level

Case : Type ℓX → Type ℓX
Case X = X × X

infix 6 _↦_
_↦_ : {W : Type ℓY} {X : Type ℓX} → W → X → W × X
w ↦ x = w , x

passes : {X : Type ℓX} → List (Case X) → Type ℓX
passes cs = List.map fst cs ≡ List.map snd cs

infix 3 _at_
_at_ : {W : Type ℓY} {X : Type ℓX}
  → (W → X) → List (W × X) → List (Case X)
f at cs = List.map (λ c → f (c .fst) ↦ c .snd) cs
