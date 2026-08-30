{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Cubical.Algebra.Theory.Finitary.Free.ClosingElim where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open import Cubical.Algebra.Theory.Finitary.Free.Closing

open SortedSig
open SortedEqns

private variable ℓ ℓ'' ℓv ℓS ℓP : Level

module _ {S : Type ℓS} {σ : SortedSig S ℓ} (σeq : SortedEqns σ ℓ'')
  {V : Type ℓv} {vs : V → S} where

  private
    Free : S → Type _
    Free = FreeModel σeq V vs

    Subst : σeq .eqns → Type _
    Subst e = (w : vars σeq e) → Free (σeq .varSort e w)

  -- The dependent eliminator.  `FreeModel` is set-truncated, so a set-valued
  -- motive is the most that can be eliminated into; at that motive none of
  -- the three path constructors is automatic, and each contributes a `PathP`
  -- method between the two sides it identifies.
  module _
    {P : {s : S} → Free s → Type ℓP}
    (isSetP : {s : S} (m : Free s) → isSet (P m))
    (pvar : (v : V) → P (var v))
    (pnode : (o : σ .ops)
        (f : (a : arities σ o) → Free (σ .sortOf o a))
      → ((a : arities σ o) → P (f a)) → P (node o f))
    (pclo : (e : σeq .eqns) {s : S}
        (t : Tm σ (vars σeq e) (σeq .varSort e) s) (ρ : Subst e)
      → ((w : vars σeq e) → P (ρ w)) → P (clo e t ρ))
    (pcloVar : (e : σeq .eqns) (w : vars σeq e) (ρ : Subst e)
        (pρ : (w' : vars σeq e) → P (ρ w'))
      → PathP (λ i → P (cloVar e w ρ i)) (pclo e (var w) ρ pρ) (pρ w))
    (pcloNode : (e : σeq .eqns) (o : σ .ops)
        (ts : (a : arities σ o)
            → Tm σ (vars σeq e) (σeq .varSort e) (σ .sortOf o a))
        (ρ : Subst e) (pρ : (w : vars σeq e) → P (ρ w))
      → PathP (λ i → P (cloNode e o ts ρ i))
          (pclo e (node o ts) ρ pρ)
          (pnode o (λ a → clo e (ts a) ρ) (λ a → pclo e (ts a) ρ pρ)))
    (peqn : (e : σeq .eqns) (ρ : Subst e)
        (pρ : (w : vars σeq e) → P (ρ w))
      → PathP (λ i → P (eqn e ρ i))
          (pclo e (σeq .lhs e) ρ pρ) (pclo e (σeq .rhs e) ρ pρ))
    where

    elim : {s : S} (m : Free s) → P m
    elim (var v) = pvar v
    elim (node o f) = pnode o f (λ a → elim (f a))
    elim (clo e t ρ) = pclo e t ρ (λ w → elim (ρ w))
    elim (cloVar e w ρ i) = pcloVar e w ρ (λ w' → elim (ρ w')) i
    elim (cloNode e o ts ρ i) = pcloNode e o ts ρ (λ w → elim (ρ w)) i
    elim (eqn e ρ i) = peqn e ρ (λ w → elim (ρ w)) i
    elim (trunc x y p q i j) =
      isSet→SquareP (λ i j → isSetP (trunc x y p q i j))
        (λ k → elim (p k)) (λ k → elim (q k))
        (λ _ → elim x) (λ _ → elim y) i j

  -- At a prop-valued motive the three path methods are forced, so only the
  -- point constructors have to be given.
  module _
    {P : {s : S} → Free s → Type ℓP}
    (isPropP : {s : S} (m : Free s) → isProp (P m))
    (pvar : (v : V) → P (var v))
    (pnode : (o : σ .ops)
        (f : (a : arities σ o) → Free (σ .sortOf o a))
      → ((a : arities σ o) → P (f a)) → P (node o f))
    (pclo : (e : σeq .eqns) {s : S}
        (t : Tm σ (vars σeq e) (σeq .varSort e) s) (ρ : Subst e)
      → ((w : vars σeq e) → P (ρ w)) → P (clo e t ρ))
    where

    elimProp : {s : S} (m : Free s) → P m
    elimProp =
      elim (λ m → isProp→isSet (isPropP m)) pvar pnode pclo
        (λ e w ρ _ → isProp→PathP (λ i → isPropP (cloVar e w ρ i)) _ _)
        (λ e o ts ρ _ → isProp→PathP (λ i → isPropP (cloNode e o ts ρ i)) _ _)
        (λ e ρ _ → isProp→PathP (λ i → isPropP (eqn e ρ i)) _ _)
