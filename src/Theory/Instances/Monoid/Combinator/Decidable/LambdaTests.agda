{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The untyped lambda decider, run on token lists.  Every `Eq.refl` below
   is the parser running; a `no-` case is a refutation of the whole
   grammar at that word, not a failure to find a parse. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Combinator.Decidable.LambdaTests where

open import Cubical.Data.List using ([] ; _∷_)
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Combinator.Decidable.Lambda

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
