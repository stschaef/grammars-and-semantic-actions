{- The uniform shape of a test case.

   A suite is ordinary external data: a list of (input, expected) rows,
   turned into a single equation between two lists so that one `refl`
   discharges the whole suite and a failure names the row that differs.
   Nothing here mentions a theory -- what makes a suite a test *of the
   DSL* is that the function under test is `run` of a semantic action. -}
open import Cubical.Foundations.Prelude
module Theory.Type.SemanticAction.Suite where

open import Cubical.Data.List using (List)
import Cubical.Data.List as List
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
import Cubical.Data.Maybe as M

private variable ℓX ℓY : Level

-- One row of a suite: the value produced, paired with the value expected.
Row : Type ℓX → Type ℓX
Row X = X × X

infix 6 _↦_
_↦_ : {W : Type ℓY} {X : Type ℓX} → W → X → W × X
w ↦ x = w , x

passes : {X : Type ℓX} → List (Row X) → Type ℓX
passes cs = List.map fst cs ≡ List.map snd cs

infix 3 _at_
_at_ : {W : Type ℓY} {X : Type ℓX}
  → (W → X) → List (W × X) → List (Row X)
f at cs = List.map (λ c → f (c .fst) ↦ c .snd) cs

-- A fallible pass, on the inputs it must accept.  `accepts` states the
-- answer, `rejects` only that there is none, so a rejection lists its
-- inputs bare.
accepts : {W : Type ℓY} {X : Type ℓX}
  → (W → M.Maybe X) → List (W × X) → Type ℓX
accepts f cs = passes (f at List.map (λ c → c .fst ↦ M.just (c .snd)) cs)

rejects : {W : Type ℓY} {X : Type ℓX}
  → (W → M.Maybe X) → List W → Type ℓX
rejects f ws = passes (f at List.map (_↦ M.nothing) ws)
