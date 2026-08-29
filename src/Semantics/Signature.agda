{-# OPTIONS --lossy-unification #-}
{- Signatures of (finitary) algebraic theories.

   The grammar DSL is generic in a theory: the theory says which
   operations are available for combining grammars, and a model is a
   category interpreting each operation as a functor that is closed in
   each of its argument slots.

   The theory of monoids is the case relevant to strings: a nullary
   operation ε and a binary operation ⊗, whose two slot-closures are
   exactly the two linear function types ⊸ and ⟜.

   Arities are required to be discrete. Every finitary theory satisfies
   this, and it is what lets us talk about "the i-th argument" of an
   operation.
-}
module Semantics.Signature where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Bool using (Bool; true; false; true≢false; false≢true)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary.Base

private
  variable
    ℓO ℓA ℓZ ℓW : Level

-- Case analysis on a decision, used to define slot update. Kept
-- top-level so that its computation rules are visible downstream.
caseDec : {P : Type ℓZ} {W : Type ℓW} → Dec P → W → W → W
caseDec (yes _) t f = t
caseDec (no _) t f = f

record Signature (ℓO ℓA : Level) : Type (ℓ-suc (ℓ-max ℓO ℓA)) where
  field
    Op : Type ℓO
    Arity : Op → Type ℓA
    DiscreteArity : (o : Op) → Discrete (Arity o)

  module _ {o : Op} {Z : Type ℓZ} where
    -- `upd γ i z` is the argument list γ with the i-th slot replaced.
    upd : (Arity o → Z) → Arity o → Z → Arity o → Z
    upd γ i z j = caseDec (DiscreteArity o j i) z (γ j)

------------------------------------------------------------------------
-- The theory of monoids
------------------------------------------------------------------------

data MonoidOp : Type ℓ-zero where
  `ε `⊗ : MonoidOp

-- Written out by hand so that it reduces on constructors, which is
-- what makes `upd` compute in the monoidal instance.
DiscreteBool : Discrete Bool
DiscreteBool true true = yes refl
DiscreteBool true false = no true≢false
DiscreteBool false true = no false≢true
DiscreteBool false false = yes refl

MonoidSig : Signature ℓ-zero ℓ-zero
MonoidSig .Signature.Op = MonoidOp
MonoidSig .Signature.Arity `ε = ⊥
MonoidSig .Signature.Arity `⊗ = Bool
MonoidSig .Signature.DiscreteArity `ε = λ ()
MonoidSig .Signature.DiscreteArity `⊗ = DiscreteBool
