{- Semantic-action stages across arbitrary algebraic theories.

   An `Input` is the exact hand-off contract for a next stage: every external
   result of the preceding action is materialised as an indexed inhabitant of
   a type in the next theory.  It is intentionally not a monoid notion.
   `then` composes the two semantic actions while keeping the intervening
   theory and its chosen input representation explicit. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Type.SemanticAction.Base
import Theory.Base
import Theory.Free.Base as FB

module Theory.Type.SemanticAction.Pipeline
  {ℓ₁ ℓ₁′ ℓV ℓS ℓ₂ ℓ₂′ ℓW ℓT ℓP ℓQ}
  {S : Type ℓS} {σ : SortedSig S ℓ₁}
  (σeq : SortedEqns σ ℓ₁′) (V : Type ℓV) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  {T : Type ℓT} {τ : SortedSig T ℓ₂}
  (τeq : SortedEqns τ ℓ₂′) (W : Type ℓW) (ws : W → T)
  (𝒬 : FB.FreePresentation τeq W ws ℓQ) where

open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)

module Source = Theory.Type.SemanticAction.Base σeq V vs 𝒫
module Target = Theory.Type.SemanticAction.Base τeq W ws 𝒬
module SourceBase = Theory.Base σeq V vs 𝒫
module TargetBase = Theory.Base τeq W ws 𝒬

private variable ℓA ℓB ℓX ℓY : Level

-- The target's chosen representation of values produced by the preceding
-- stage.  In the monoid instance this is `Strings.read`; another
-- theory may choose a tree, store, context, or any other indexed input.
record Input {t : T} (X : Type ℓX) (B : TargetBase.TheoryTy ℓB t)
  : Type (ℓ-max ℓX (ℓ-max TargetBase.ℓM ℓB)) where
  field
    world  : X → TargetBase.↓M t
    inhabit : (x : X) → B (world x)

open Input public

feed : {t : T} {X : Type ℓX} {Y : Type ℓY} {B : TargetBase.TheoryTy ℓB t}
  → Input X B → Target.SemanticAction B Y → X → Y
feed i b x = b (world i x) (inhabit i x) .fst

-- Semantic actions compose through an input contract even when their source
-- and target theories differ.  The resulting action remains indexed by the
-- first theory's input, as a compiler stage should.
then : {s : S} {t : T} {A : SourceBase.TheoryTy ℓA s}
  {B : TargetBase.TheoryTy ℓB t} {X : Type ℓX} {Y : Type ℓY}
  → Source.SemanticAction A X → Input X B → Target.SemanticAction B Y
  → Source.SemanticAction A Y
then a i b m p = feed i b (a m p .fst) , tt

-- The usual compiler boundary is fallible (lexing and parsing).  Failure is
-- propagated without inventing an input for the next theory; success uses
-- exactly the same `Input` contract as `then`.
thenMaybe : {s : S} {t : T} {A : SourceBase.TheoryTy ℓA s}
  {B : TargetBase.TheoryTy ℓB t} {X : Type ℓX} {Y : Type ℓY}
  → Source.SemanticAction A (Maybe X) → Input X B → Target.SemanticAction B (Maybe Y)
  → Source.SemanticAction A (Maybe Y)
thenMaybe a i b m p with a m p .fst
... | nothing = nothing , tt
... | just x = feed i b x , tt
