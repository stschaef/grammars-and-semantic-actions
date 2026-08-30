{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The arrow/member decider, run on token lists.  The interesting cases
   are the ones where the two bracket productions share an unbounded
   prefix, so the answer is fixed only once the `(` has been matched.
   Every `no-` case is a refutation, not a failure to find a parse. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Combinator.Decidable.ArrowTests where

open import Cubical.Data.List using ([] ; _∷_)
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Combinator.Decidable.Arrow

-- Accepted

yes-id : L (vid ∷ [])
yes-id = theYes (parse (vid ∷ []) tt) Eq.refl

-- (x) => x
yes-arrow : L (lp ∷ vid ∷ rp ∷ ar ∷ vid ∷ [])
yes-arrow = theYes (parse (lp ∷ vid ∷ rp ∷ ar ∷ vid ∷ []) tt) Eq.refl

-- (x, y) => x
yes-arrow2 : L (lp ∷ vid ∷ cm ∷ vid ∷ rp ∷ ar ∷ vid ∷ [])
yes-arrow2 = theYes (parse (lp ∷ vid ∷ cm ∷ vid ∷ rp ∷ ar ∷ vid ∷ []) tt) Eq.refl

-- (x, y, z) => x
yes-arrow3 : L (lp ∷ vid ∷ cm ∷ vid ∷ cm ∷ vid ∷ rp ∷ ar ∷ vid ∷ [])
yes-arrow3 =
  theYes (parse (lp ∷ vid ∷ cm ∷ vid ∷ cm ∷ vid ∷ rp ∷ ar ∷ vid ∷ []) tt) Eq.refl

-- (x).f
yes-member : L (lp ∷ vid ∷ rp ∷ dot ∷ vid ∷ [])
yes-member = theYes (parse (lp ∷ vid ∷ rp ∷ dot ∷ vid ∷ []) tt) Eq.refl

-- ((x) => x).f  -- the outer `(` is resolved only after matching it
yes-nested : L (lp ∷ lp ∷ vid ∷ rp ∷ ar ∷ vid ∷ rp ∷ dot ∷ vid ∷ [])
yes-nested =
  theYes (parse (lp ∷ lp ∷ vid ∷ rp ∷ ar ∷ vid ∷ rp ∷ dot ∷ vid ∷ []) tt) Eq.refl

-- (x) => (x).f
yes-body : L (lp ∷ vid ∷ rp ∷ ar ∷ lp ∷ vid ∷ rp ∷ dot ∷ vid ∷ [])
yes-body =
  theYes (parse (lp ∷ vid ∷ rp ∷ ar ∷ lp ∷ vid ∷ rp ∷ dot ∷ vid ∷ []) tt) Eq.refl

-- ((x, y) => x).f
yes-deep : L (lp ∷ lp ∷ vid ∷ cm ∷ vid ∷ rp ∷ ar ∷ vid ∷ rp ∷ dot ∷ vid ∷ [])
yes-deep =
  theYes (parse (lp ∷ lp ∷ vid ∷ cm ∷ vid ∷ rp ∷ ar ∷ vid ∷ rp ∷ dot ∷ vid ∷ [])
    tt) Eq.refl

-- Refuted

no-nil : ¬Ty L []
no-nil = theNo (parse [] tt) Eq.refl

-- (x)  -- a bracket with neither `=>` nor `.f` after it
no-bare : ¬Ty L (lp ∷ vid ∷ rp ∷ [])
no-bare = theNo (parse (lp ∷ vid ∷ rp ∷ []) tt) Eq.refl

-- (x) =>  -- no body
no-nobody : ¬Ty L (lp ∷ vid ∷ rp ∷ ar ∷ [])
no-nobody = theNo (parse (lp ∷ vid ∷ rp ∷ ar ∷ []) tt) Eq.refl

-- (x,) => x  -- trailing comma
no-trailing : ¬Ty L (lp ∷ vid ∷ cm ∷ rp ∷ ar ∷ vid ∷ [])
no-trailing = theNo (parse (lp ∷ vid ∷ cm ∷ rp ∷ ar ∷ vid ∷ []) tt) Eq.refl

-- x.f  -- member access needs the parens
no-unparen : ¬Ty L (vid ∷ dot ∷ vid ∷ [])
no-unparen = theNo (parse (vid ∷ dot ∷ vid ∷ []) tt) Eq.refl

no-close : ¬Ty L (rp ∷ [])
no-close = theNo (parse (rp ∷ []) tt) Eq.refl

-- ((x) => x)  -- matched, but nothing after the match
no-nested-bare : ¬Ty L (lp ∷ lp ∷ vid ∷ rp ∷ ar ∷ vid ∷ rp ∷ [])
no-nested-bare =
  theNo (parse (lp ∷ lp ∷ vid ∷ rp ∷ ar ∷ vid ∷ rp ∷ []) tt) Eq.refl
