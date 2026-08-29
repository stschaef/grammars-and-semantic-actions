{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- One matcher, three answers -- and here, for the first time in this
   development, the three say different things.

   For a single pattern they cannot: `Match p` is a proposition, so `Dec`,
   `Maybe` and `ND` agree up to the shape of their answer, exactly as they
   did for typing.  A *clause list* is a sum, and a sum is where they part:

     `Dec`    does some clause fire, with a refutation when none does
     `Maybe`  the leftmost clause that fires, and its bindings -- the
              first-match semantics every real pattern matcher implements
     `ND`     every clause that fires

   So `tally` is a static analysis and not a decision.  Two means the
   clause list is redundant at this value -- two clauses claim it, and the
   `Maybe` answer silently discarded one.  Zero means the value is a
   counterexample to exhaustiveness.  Neither number is recoverable from
   the other two answers; this is what the nondeterministic reading is for,
   and it costs nothing, because the grammar was written once.

   The tests are `refl`, so the typechecker runs the matcher. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Match.Tests where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (_,_)

open import Theory.Instances.Match.Bindings
open import Theory.Instances.Match.Exhaustive using (full ; covers)

-- clause lists
shared : List Pat                  -- (true , _) | (_ , true)
shared = ppair ptrue pwild ∷ ppair pwild ptrue ∷ []

sharedV : List Pat                 -- (x , _) | (_ , y)
sharedV = ppair (pvar 0) pwild ∷ ppair pwild (pvar 1) ∷ []

partial : List Pat                  -- true
partial = ptrue ∷ []

-- `full`, the complete list, is `Exhaustive`'s: the tests below are the
-- computational shadow of `covers`.
swap : List Pat                     -- (x , y)
swap = ppair (pvar 0) (pvar 1) ∷ []

-- values
tt' ff' : Val
tt' = vtrue
ff' = vfalse

both : Val
both = vpair vtrue vtrue

mixed : Val
mixed = vpair vtrue vfalse

deep : Val
deep = vpair (vpair vtrue vfalse) vtrue


-- A single pattern is unambiguous, so the three answers agree.
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


-- `Dec`: does some clause fire?
dec-shared : decideMatch shared both ≡ just (0 , [])
dec-shared = refl

dec-partial-yes : decideMatch partial tt' ≡ just (0 , [])
dec-partial-yes = refl

-- ...and a refutation when none does
dec-partial-no : decideMatch partial ff' ≡ nothing
dec-partial-no = refl

dec-empty : decideMatch [] both ≡ nothing
dec-empty = refl


-- `Maybe`: the first clause that fires, with its bindings.  Note the third
-- clause of `full` is never reached at `tt'`, and the second clause of
-- `sharedV` is never reached at all.
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


-- `ND`: every clause that fires.  This is the deliverable -- the count is
-- a fact about the clause list that neither other answer can express.

-- two clauses claim the same value: the list is redundant here
nd-redundant : tally shared both ≡ 2
nd-redundant = refl

-- ...and the second derivation is the one `Maybe` threw away
nd-redundant-all : allMatches shared both ≡ (0 , []) ∷ (1 , []) ∷ []
nd-redundant-all = refl

-- with binders, the two derivations bind *different* variables
nd-sharedV : allMatches sharedV mixed
            ≡ (0 , (0 , vtrue) ∷ []) ∷ (1 , (1 , vfalse) ∷ []) ∷ []
nd-sharedV = refl

nd-sharedV-count : tally sharedV mixed ≡ 2
nd-sharedV-count = refl

-- no clause claims this value: it is a counterexample to exhaustiveness
nd-nonexhaustive : tally partial ff' ≡ 0
nd-nonexhaustive = refl

nd-nonexhaustive-pair : tally shared (vpair vfalse vfalse) ≡ 0
nd-nonexhaustive-pair = refl

nd-empty : tally [] both ≡ 0
nd-empty = refl

-- ...and the same list is fine at a value it does cover
nd-partial-hit : tally partial tt' ≡ 1
nd-partial-hit = refl

-- a complete, irredundant list: exactly one clause fires, at every head
nd-full-true : tally full tt' ≡ 1
nd-full-true = refl

nd-full-false : tally full ff' ≡ 1
nd-full-false = refl

nd-full-pair : tally full deep ≡ 1
nd-full-pair = refl

nd-swap : allMatches swap mixed ≡ (0 , (0 , vtrue) ∷ (1 , vfalse) ∷ []) ∷ []
nd-swap = refl
