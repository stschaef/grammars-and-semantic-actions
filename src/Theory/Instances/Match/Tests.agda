{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- One pattern: the answers agree (`Match p` is a proposition).  A clause
   list is a sum, where they part:
     `Dec`    does some clause fire (refutation when none)
     `Maybe`  leftmost clause that fires -- first-match semantics
     `ND`     every clause that fires
   Tests are `refl`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Match.Tests where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)

open import Theory.Instances.Match.Bindings
open import Theory.Instances.Match.Exhaustive using (full ; covers)

shared : List Pat                  -- (true , _) | (_ , true)
shared = ppair ptrue pwild ∷ ppair pwild ptrue ∷ []

sharedV : List Pat                 -- (x , _) | (_ , y)
sharedV = ppair (pvar 0) pwild ∷ ppair pwild (pvar 1) ∷ []

partial : List Pat                  -- true
partial = ptrue ∷ []

-- `full` is `Exhaustive`'s complete list; these tests shadow `covers`.
swap : List Pat                     -- (x , y)
swap = ppair (pvar 0) (pvar 1) ∷ []

tt' ff' : Val
tt' = vtrue
ff' = vfalse

both : Val
both = vpair vtrue vtrue

mixed : Val
mixed = vpair vtrue vfalse

deep : Val
deep = vpair (vpair vtrue vfalse) vtrue

one-pair : bindsOf (ppair (pvar 0) (pvar 1)) mixed
         ≡ just ((0 , vtrue) ∷ (1 , vfalse) ∷ [])
one-pair = refl

one-wild : bindsOf pwild deep ≡ just []
one-wild = refl

one-clash : bindsOf ptrue ff' ≡ nothing
one-clash = refl

one-shape : bindsOf (ppair pwild pwild) tt' ≡ nothing
one-shape = refl

one-nested : bindsOf (ppair (ppair (pvar 0) (pvar 1)) (pvar 2)) deep
           ≡ just ((0 , vtrue) ∷ (1 , vfalse) ∷ (2 , vtrue) ∷ [])
one-nested = refl

dec-shared : decideMatch shared both ≡ just (0 , [])
dec-shared = refl

dec-partial-yes : decideMatch partial tt' ≡ just (0 , [])
dec-partial-yes = refl

dec-partial-no : decideMatch partial ff' ≡ nothing
dec-partial-no = refl

dec-empty : decideMatch [] both ≡ nothing
dec-empty = refl

may-full-true : firstMatch full tt' ≡ just (0 , [])
may-full-true = refl

may-full-false : firstMatch full ff' ≡ just (1 , [])
may-full-false = refl

may-full-pair : firstMatch full mixed ≡ just (2 , [])
may-full-pair = refl

may-sharedV : firstMatch sharedV mixed ≡ just (0 , (0 , vtrue) ∷ [])
may-sharedV = refl

may-partial-no : firstMatch partial ff' ≡ nothing
may-partial-no = refl

nd-redundant : tally shared both ≡ 2
nd-redundant = refl

nd-redundant-all : allMatches shared both ≡ (0 , []) ∷ (1 , []) ∷ []
nd-redundant-all = refl

-- the two derivations bind *different* variables
nd-sharedV : allMatches sharedV mixed
            ≡ (0 , (0 , vtrue) ∷ []) ∷ (1 , (1 , vfalse) ∷ []) ∷ []
nd-sharedV = refl

nd-sharedV-count : tally sharedV mixed ≡ 2
nd-sharedV-count = refl

nd-nonexhaustive : tally partial ff' ≡ 0
nd-nonexhaustive = refl

nd-nonexhaustive-pair : tally shared (vpair vfalse vfalse) ≡ 0
nd-nonexhaustive-pair = refl

nd-empty : tally [] both ≡ 0
nd-empty = refl

nd-partial-hit : tally partial tt' ≡ 1
nd-partial-hit = refl

nd-full-true : tally full tt' ≡ 1
nd-full-true = refl

nd-full-false : tally full ff' ≡ 1
nd-full-false = refl

nd-full-pair : tally full deep ≡ 1
nd-full-pair = refl

nd-swap : allMatches swap mixed ≡ (0 , (0 , vtrue) ∷ (1 , vfalse) ∷ []) ∷ []
nd-swap = refl

carries : (p : Pat) (v : Val) (d : Match p v) → inst p (d .fst) ≡ v
carries p v d = d .snd

-- non-linear: still a proposition (`Env` is per occurrence), still binds twice
nonlinear : List Pat
nonlinear = ppair (pvar 0) (pvar 0) ∷ []

nd-nonlinear : allMatches nonlinear mixed
             ≡ (0 , (0 , vtrue) ∷ (0 , vfalse) ∷ []) ∷ []
nd-nonlinear = refl

nd-nonlinear-count : tally nonlinear mixed ≡ 1
nd-nonlinear-count = refl
