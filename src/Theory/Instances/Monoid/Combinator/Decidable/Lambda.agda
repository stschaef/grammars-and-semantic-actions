{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Untyped lambda terms, predictively.

     t ::= λ v . t | ( t t ) | v

   Application is parenthesised, so the grammar is left-recursion-free and
   every production is terminal-led: `λ`, `(` and `v` name three classes and
   the rest have none.  One nonterminal, not nullable. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Combinator.Decidable.Lambda where

open import Cubical.Data.Bool using (false)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Unit using (Unit ; tt)

data Tok : Type ℓ-zero where
  lam dot lp rp v : Tok

_≟T_ : (x y : Tok) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
lam ≟T lam = Sum.inl Eq.refl
lam ≟T dot = Sum.inr λ ()
lam ≟T lp = Sum.inr λ ()
lam ≟T rp = Sum.inr λ ()
lam ≟T v = Sum.inr λ ()
dot ≟T lam = Sum.inr λ ()
dot ≟T dot = Sum.inl Eq.refl
dot ≟T lp = Sum.inr λ ()
dot ≟T rp = Sum.inr λ ()
dot ≟T v = Sum.inr λ ()
lp ≟T lam = Sum.inr λ ()
lp ≟T dot = Sum.inr λ ()
lp ≟T lp = Sum.inl Eq.refl
lp ≟T rp = Sum.inr λ ()
lp ≟T v = Sum.inr λ ()
rp ≟T lam = Sum.inr λ ()
rp ≟T dot = Sum.inr λ ()
rp ≟T lp = Sum.inr λ ()
rp ≟T rp = Sum.inl Eq.refl
rp ≟T v = Sum.inr λ ()
v ≟T lam = Sum.inr λ ()
v ≟T dot = Sum.inr λ ()
v ≟T lp = Sum.inr λ ()
v ≟T rp = Sum.inr λ ()
v ≟T v = Sum.inl Eq.refl

open import Theory.Instances.Monoid.Combinator.Decidable.Productions Tok _≟T_

lamTable : Table Unit
lamTable .Table.at _ ε₁ = none
lamTable .Table.at _ (tk lam) = led (tm v ∷ tm dot ∷ nt tt ∷ [])
lamTable .Table.at _ (tk dot) = none
lamTable .Table.at _ (tk lp) = led (nt tt ∷ nt tt ∷ tm rp ∷ [])
lamTable .Table.at _ (tk rp) = none
lamTable .Table.at _ (tk v) = led []
lamTable .Table.nul _ = false

open Gen lamTable

Term : TheoryTy ℓG tt
Term = S tt

parse : Decidable Term
parse = decide tt

------------------------------------------------------------------------
-- Every `Eq.refl` below is the parser running.

yes-v : Term (v ∷ [])
yes-v = theYes (parse (v ∷ []) tt) Eq.refl

yes-id : Term (lam ∷ v ∷ dot ∷ v ∷ [])
yes-id = theYes (parse (lam ∷ v ∷ dot ∷ v ∷ []) tt) Eq.refl

yes-app : Term (lp ∷ v ∷ v ∷ rp ∷ [])
yes-app = theYes (parse (lp ∷ v ∷ v ∷ rp ∷ []) tt) Eq.refl

yes-omega : Term (lp ∷ lam ∷ v ∷ dot ∷ lp ∷ v ∷ v ∷ rp ∷ lam ∷ v ∷ dot ∷ lp ∷ v ∷ v ∷ rp ∷ rp ∷ [])
yes-omega = theYes
  (parse (lp ∷ lam ∷ v ∷ dot ∷ lp ∷ v ∷ v ∷ rp ∷ lam ∷ v ∷ dot ∷ lp ∷ v ∷ v ∷ rp ∷ rp ∷ []) tt)
  Eq.refl

no-nil : ¬Ty Term []
no-nil = theNo (parse [] tt) Eq.refl

no-dot : ¬Ty Term (dot ∷ [])
no-dot = theNo (parse (dot ∷ []) tt) Eq.refl

no-unclosed : ¬Ty Term (lp ∷ v ∷ v ∷ [])
no-unclosed = theNo (parse (lp ∷ v ∷ v ∷ []) tt) Eq.refl

no-juxt : ¬Ty Term (v ∷ v ∷ [])
no-juxt = theNo (parse (v ∷ v ∷ []) tt) Eq.refl

no-lam-noarg : ¬Ty Term (lam ∷ v ∷ dot ∷ [])
no-lam-noarg = theNo (parse (lam ∷ v ∷ dot ∷ []) tt) Eq.refl
