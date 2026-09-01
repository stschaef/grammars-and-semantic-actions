{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Stress cases, kept as a regression guard.  Wall time minus the ~2.9s of
   interface loading:

     ((a|b)*)\1 on 128 chars, match and no-match      ~0.5s
     (a|b)*     on 128 chars (no backreference)        ~0.3s
     (a^32)\1   on 64 chars                            ~0.0s
     15-deep nested groups, then \1                    ~0.0s
     ((a|aa)*)\1 on a^n b, no-match:  n=8  ~0.6s
                                      n=12 ~2.6s
                                      n=16 ~22s
                                      n=20 killed at 376s

   An unambiguous group is linear-ish; a backreference roughly doubles the
   star's cost (a second left-to-right pass).  An ambiguous group is
   exponential in the REFUTATION direction: `_<|>_` decides both branches
   (`▷dec-⊕&` needs both) -- backreference NP-hardness, a property of
   `_<|>_` and not `⊗ᴰ` (`AmbigPos20` finds its witness in ~1.3s). -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Maybe as M

module Examples.Theory.Backreference.Stress where

open import Examples.Theory.Backreference.StressCommon

-- CopyPos128
_ : matches copyRE (a ∷ b ∷ b ∷ a ∷ a ∷ b ∷ b ∷ b ∷ b ∷ b ∷ a ∷ a ∷ b ∷ b ∷ a ∷ a ∷ b ∷ b ∷ b ∷ b ∷ b ∷ a ∷ b ∷ b ∷ a ∷ a ∷ b ∷ a ∷ a ∷ b ∷ a ∷ a ∷ b ∷ b ∷ b ∷ a ∷ a ∷ b ∷ b ∷ b ∷ a ∷ b ∷ b ∷ b ∷ b ∷ b ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ b ∷ a ∷ b ∷ b ∷ a ∷ a ∷ b ∷ b ∷ b ∷ a ∷ a ∷ b ∷ b ∷ a ∷ a ∷ b ∷ b ∷ b ∷ b ∷ b ∷ a ∷ a ∷ b ∷ b ∷ a ∷ a ∷ b ∷ b ∷ b ∷ b ∷ b ∷ a ∷ b ∷ b ∷ a ∷ a ∷ b ∷ a ∷ a ∷ b ∷ a ∷ a ∷ b ∷ b ∷ b ∷ a ∷ a ∷ b ∷ b ∷ b ∷ a ∷ b ∷ b ∷ b ∷ b ∷ b ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ b ∷ a ∷ b ∷ b ∷ a ∷ a ∷ b ∷ b ∷ b ∷ a ∷ []) ≡ M.just tt
_ = refl

-- CopyNeg128
_ : matches copyRE (b ∷ b ∷ b ∷ a ∷ a ∷ b ∷ a ∷ a ∷ b ∷ b ∷ a ∷ a ∷ a ∷ b ∷ b ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ b ∷ b ∷ b ∷ a ∷ a ∷ b ∷ b ∷ a ∷ a ∷ b ∷ b ∷ b ∷ a ∷ b ∷ b ∷ a ∷ b ∷ a ∷ a ∷ a ∷ b ∷ a ∷ b ∷ b ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ b ∷ b ∷ b ∷ b ∷ a ∷ a ∷ b ∷ b ∷ a ∷ b ∷ b ∷ b ∷ b ∷ b ∷ a ∷ a ∷ b ∷ a ∷ a ∷ b ∷ b ∷ a ∷ a ∷ a ∷ b ∷ b ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ b ∷ b ∷ b ∷ a ∷ a ∷ b ∷ b ∷ a ∷ a ∷ b ∷ b ∷ b ∷ a ∷ b ∷ b ∷ a ∷ b ∷ a ∷ a ∷ a ∷ b ∷ a ∷ b ∷ b ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ b ∷ b ∷ b ∷ b ∷ a ∷ a ∷ b ∷ b ∷ a ∷ b ∷ a ∷ []) ≡ M.nothing
_ = refl

-- StarPos128
_ : matches starRE (a ∷ b ∷ b ∷ a ∷ b ∷ b ∷ b ∷ a ∷ b ∷ a ∷ b ∷ a ∷ b ∷ a ∷ b ∷ b ∷ b ∷ a ∷ a ∷ b ∷ a ∷ a ∷ b ∷ a ∷ a ∷ b ∷ a ∷ b ∷ a ∷ b ∷ a ∷ a ∷ b ∷ b ∷ a ∷ a ∷ a ∷ b ∷ b ∷ b ∷ b ∷ a ∷ b ∷ b ∷ a ∷ b ∷ a ∷ b ∷ b ∷ b ∷ a ∷ b ∷ b ∷ b ∷ a ∷ a ∷ a ∷ a ∷ a ∷ b ∷ b ∷ a ∷ a ∷ b ∷ a ∷ b ∷ b ∷ b ∷ a ∷ b ∷ b ∷ a ∷ b ∷ a ∷ a ∷ b ∷ a ∷ b ∷ a ∷ a ∷ b ∷ a ∷ a ∷ a ∷ b ∷ a ∷ b ∷ a ∷ b ∷ b ∷ b ∷ a ∷ a ∷ a ∷ a ∷ a ∷ b ∷ a ∷ a ∷ a ∷ b ∷ b ∷ a ∷ b ∷ b ∷ a ∷ b ∷ b ∷ a ∷ b ∷ a ∷ a ∷ a ∷ a ∷ b ∷ a ∷ b ∷ a ∷ b ∷ b ∷ b ∷ b ∷ a ∷ a ∷ b ∷ a ∷ a ∷ b ∷ []) ≡ M.just tt
_ = refl

-- LitBack32
_ : matches (litbackRE 31) (a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ []) ≡ M.just tt
_ = refl

-- Deep15
_ : matches (deepRE 15) (a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ []) ≡ M.just tt
_ = refl

-- TwicePos
_ : matches twiceRE (a ∷ a ∷ a ∷ []) ≡ M.just tt
_ = refl

-- TwiceNeg
_ : matches twiceRE (a ∷ b ∷ a ∷ []) ≡ M.nothing
_ = refl

-- AmbigPos20
_ : matches ambigRE (a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ []) ≡ M.just tt
_ = refl

-- AmbigNeg12
_ : matches ambigRE (a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ b ∷ []) ≡ M.nothing
_ = refl
