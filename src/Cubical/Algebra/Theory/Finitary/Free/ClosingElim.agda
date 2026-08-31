{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- The prop-eliminator the closing HIT was missing.  `rec` is non-dependent,
   so a dependent statement about a fold -- monotonicity, say -- could only be
   had by transporting along `recUniq`, and that transport is opaque: it does
   not reduce even at a single generator.  At a prop-valued motive every path
   constructor is automatic, so this costs three cases. -}
module Cubical.Algebra.Theory.Finitary.Free.ClosingElim where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open import Cubical.Algebra.Theory.Finitary.Free.Closing

open SortedSig
open SortedEqns

private variable ℓ ℓ'' ℓv ℓS ℓP : Level

module _ {S : Type ℓS} {σ : SortedSig S ℓ} (σeq : SortedEqns σ ℓ'')
  {V : Type ℓv} {vs : V → S}
  {P : {s : S} → FreeModel σeq V vs s → Type ℓP}
  (isPropP : {s : S} (m : FreeModel σeq V vs s) → isProp (P m))
  (pvar : (v : V) → P (var v))
  (pnode : (o : σ .ops)
      (f : (a : arities σ o) → FreeModel σeq V vs (σ .sortOf o a))
    → ((a : arities σ o) → P (f a)) → P (node o f))
  (pclo : (e : σeq .eqns) {s : S}
      (t : Tm σ (vars σeq e) (σeq .varSort e) s)
      (ρ : (w : vars σeq e) → FreeModel σeq V vs (σeq .varSort e w))
    → ((w : vars σeq e) → P (ρ w)) → P (clo e t ρ))
  where

  elimProp : {s : S} (m : FreeModel σeq V vs s) → P m
  elimProp (var v) = pvar v
  elimProp (node o f) = pnode o f (λ a → elimProp (f a))
  elimProp (clo e t ρ) = pclo e t ρ (λ w → elimProp (ρ w))
  elimProp (cloVar e w ρ i) =
    isProp→PathP (λ i → isPropP (cloVar e w ρ i))
      (pclo e (var w) ρ (λ w' → elimProp (ρ w')))
      (elimProp (ρ w)) i
  elimProp (cloNode e o ts ρ i) =
    isProp→PathP (λ i → isPropP (cloNode e o ts ρ i))
      (pclo e (node o ts) ρ (λ w → elimProp (ρ w)))
      (pnode o (λ a → clo e (ts a) ρ)
        (λ a → pclo e (ts a) ρ (λ w → elimProp (ρ w)))) i
  elimProp (eqn e ρ i) =
    isProp→PathP (λ i → isPropP (eqn e ρ i))
      (pclo e (σeq .lhs e) ρ (λ w → elimProp (ρ w)))
      (pclo e (σeq .rhs e) ρ (λ w → elimProp (ρ w))) i
  elimProp (trunc x y p q i j) =
    isSet→SquareP (λ i j → isProp→isSet (isPropP (trunc x y p q i j)))
      (λ i → elimProp (p i)) (λ i → elimProp (q i))
      (λ _ → elimProp x) (λ _ → elimProp y) i j
