{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- One layout rule, three answers, and the rendered stream.  The tests are
   `refl`, so the typechecker runs them.

   `ND` counts one derivation for every accepted stream and zero for every
   rejected one, which is the expected answer and not a lucky one: the
   judgment is a proposition by construction -- `isPropLayout` is two lines
   -- because each token's rule is selected by the head constructor and
   each premise's index is a function of the state and the token.  Layout
   is deterministic, and here that is a typing fact rather than a theorem
   about the algorithm. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Layout.OffsideTests where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Sum as Sum

open import Theory.Instances.Layout.Render

import Theory.Combinator.Answer.Decidable LEqns ⊥ noVar lPresentation as D
import Theory.Combinator.Answer.Incomplete LEqns ⊥ noVar lPresentation as MB
import Theory.Combinator.Answer.NonDet LEqns ⊥ noVar lPresentation as NDm

module CM = Check MB.MaybeAnswer
module CN = Check NDm.NDAnswer

-- the same grammar, read three ways
decideLayout : (S : LState) → D.Decidable (Layout S)
decideLayout = CD.laidOut

testLayout : (S : LState) → ⊤Ty ⊢ MB.Maybe (Layout S)
testLayout = CM.laidOut

parsesLayout : (S : LState) → ⊤Ty ⊢ NDm.ND (Layout S)
parsesLayout = CN.laidOut

decB : TokList → Bool
decB ts = Sum.rec (λ _ → true) (λ _ → false) (decideLayout topLevel ts tt)

mayB : TokList → Bool
mayB ts = Sum.rec (λ _ → true) (λ _ → false) (testLayout topLevel ts tt)

count : TokList → ℕ
count ts = length (NDm.ndToList ts (parsesLayout topLevel ts tt))

-- A source file, spelled as (kind, column) pairs.  `toks` is only sugar;
-- `TokList` is the model.
toks : List Tok → TokList
toks [] = tnil
toks (t ∷ ts) = tcons t (toks ts)

x y f g h a b : TokKind
x = kid 0
y = kid 1
g = kid 2
a = kid 3
h = kid 4
b = kid 5
f = kid 6

n1 n2 : TokKind
n1 = kid 11
n2 = kid 12

--   let x = 1
--       y = 2
--   in  x
letIn : TokList
letIn = toks
  ( (klet , 1) ∷ (x , 5) ∷ (keq , 7) ∷ (n1 , 9)
  ∷ (y , 5) ∷ (keq , 7) ∷ (n2 , 9)
  ∷ (kin , 1) ∷ (x , 5) ∷ [] )

--   let g = a
--             where h = b
--   in  g
whereNest : TokList
whereNest = toks
  ( (klet , 1) ∷ (g , 5) ∷ (keq , 7) ∷ (a , 9)
  ∷ (kwhere , 11) ∷ (h , 17) ∷ (keq , 19) ∷ (b , 21)
  ∷ (kin , 1) ∷ (g , 5) ∷ [] )

--   let f = let g = 1
--       h = 2
mixed : TokList
mixed = toks
  ( (klet , 1) ∷ (f , 5) ∷ (keq , 7)
  ∷ (klet , 9) ∷ (g , 13) ∷ (keq , 15) ∷ (n1 , 17)
  ∷ (h , 5) ∷ (keq , 7) ∷ (n2 , 9) ∷ [] )

--   let x = 1 in x        -- all on one line
oneLine : TokList
oneLine = toks
  ( (klet , 1) ∷ (x , 5) ∷ (keq , 7) ∷ (n1 , 9)
  ∷ (kin , 11) ∷ (x , 14) ∷ [] )

--   f = 1
flat : TokList
flat = toks ( (f , 1) ∷ (keq , 3) ∷ (n1 , 5) ∷ [] )

--   let g = a
--     where h = b        -- the block opened by `where` starts left of `g`
badIndent : TokList
badIndent = toks
  ( (klet , 1) ∷ (g , 5) ∷ (kwhere , 7) ∷ (h , 5) ∷ [] )

--   let                  -- ...and then nothing
dangling : TokList
dangling = toks ( (klet , 1) ∷ [] )

--   let g = a
--   h = b                -- the item is not indented past `let`'s block
outdented : TokList
outdented = toks
  ( (klet , 1) ∷ (g , 5) ∷ (keq , 7) ∷ (a , 9) ∷ (h , 1) ∷ [] )


-- Acceptance, at `Dec`.
dec-letIn : decB letIn ≡ true
dec-letIn = refl

dec-whereNest : decB whereNest ≡ true
dec-whereNest = refl

dec-mixed : decB mixed ≡ true
dec-mixed = refl

dec-flat : decB flat ≡ true
dec-flat = refl

-- A block must be indented strictly past the block it sits in.
dec-badIndent : decB badIndent ≡ false
dec-badIndent = refl

-- ...and a block opener at the end of input has no block.
dec-dangling : decB dangling ≡ false
dec-dangling = refl

-- Outdenting past a block is *not* an error: it closes the block.  `h` at
-- column 1 pops the block at column 5 and lands at top level.
dec-outdented : decB outdented ≡ true
dec-outdented = refl

-- `Maybe` agrees.
may-letIn : mayB letIn ≡ true
may-letIn = refl

may-mixed : mayB mixed ≡ true
may-mixed = refl

may-badIndent : mayB badIndent ≡ false
may-badIndent = refl

may-dangling : mayB dangling ≡ false
may-dangling = refl

-- ...and `ND` finds exactly one derivation, since layout is deterministic.
nd-letIn : count letIn ≡ 1
nd-letIn = refl

nd-whereNest : count whereNest ≡ 1
nd-whereNest = refl

nd-mixed : count mixed ≡ 1
nd-mixed = refl

nd-badIndent : count badIndent ≡ 0
nd-badIndent = refl

nd-dangling : count dangling ≡ 0
nd-dangling = refl


-- The rendered stream.  This is the point: the derivation *is* the output.
--
--   let { x = 1 ; y = 2 } in x
render-letIn : layout letIn
  ≡ just ( oTok (klet , 1) ∷ oOpen ∷ oTok (x , 5) ∷ oTok (keq , 7)
         ∷ oTok (n1 , 9) ∷ oSemi ∷ oTok (y , 5) ∷ oTok (keq , 7)
         ∷ oTok (n2 , 9) ∷ oClose ∷ oTok (kin , 1) ∷ oTok (x , 5) ∷ [] )
render-letIn = refl

-- Two blocks close at once: `in` at column 1 outdents past both the
-- `where` block at 17 and the `let` block at 5.
--
--   let { g = a where { h = b } } in g
render-whereNest : layout whereNest
  ≡ just ( oTok (klet , 1) ∷ oOpen ∷ oTok (g , 5) ∷ oTok (keq , 7)
         ∷ oTok (a , 9) ∷ oTok (kwhere , 11) ∷ oOpen ∷ oTok (h , 17)
         ∷ oTok (keq , 19) ∷ oTok (b , 21) ∷ oClose ∷ oClose
         ∷ oTok (kin , 1) ∷ oTok (g , 5) ∷ [] )
render-whereNest = refl

-- The non-obvious placement: `h` at column 5 both *closes* the inner block
-- at column 13 and *starts a new item* in the outer one at column 5, so a
-- `}` and a `;` are emitted back to back, in that order, before it.  A
-- reader guessing from the source text would very likely guess `; }`.
--
--   let { f = let { g = 1 } ; h = 2 }
render-mixed : layout mixed
  ≡ just ( oTok (klet , 1) ∷ oOpen ∷ oTok (f , 5) ∷ oTok (keq , 7)
         ∷ oTok (klet , 9) ∷ oOpen ∷ oTok (g , 13) ∷ oTok (keq , 15)
         ∷ oTok (n1 , 17) ∷ oClose ∷ oSemi ∷ oTok (h , 5)
         ∷ oTok (keq , 7) ∷ oTok (n2 , 9) ∷ oClose ∷ [] )
render-mixed = refl

-- No block is ever opened, so nothing is inserted -- not even a `;` at the
-- top level, since the top-level stack is empty rather than holding a
-- column.
render-flat : layout flat
  ≡ just ( oTok (f , 1) ∷ oTok (keq , 3) ∷ oTok (n1 , 5) ∷ [] )
render-flat = refl

-- Outdenting to column 1 closes the block and emits no `;`, because the
-- surviving stack is empty: there is no enclosing block for `h` to be an
-- item of.
render-outdented : layout outdented
  ≡ just ( oTok (klet , 1) ∷ oOpen ∷ oTok (g , 5) ∷ oTok (keq , 7)
         ∷ oTok (a , 9) ∷ oClose ∷ oTok (h , 1) ∷ [] )
render-outdented = refl

-- The honest limitation, as a test.  Without Haskell's `parse-error(t)`
-- rule the `in` is just another token indented past the block, so the
-- block runs to the end of input and the `}` comes *after* `in x` instead
-- of before `in`.  The stream is accepted by layout and would be rejected
-- by any parser.  This is what a one-line `let` costs.
render-oneLine : layout oneLine
  ≡ just ( oTok (klet , 1) ∷ oOpen ∷ oTok (x , 5) ∷ oTok (keq , 7)
         ∷ oTok (n1 , 9) ∷ oTok (kin , 11) ∷ oTok (x , 14) ∷ oClose ∷ [] )
render-oneLine = refl

-- A rejected stream renders as `nothing`, not as a malformed one.
render-badIndent : layout badIndent ≡ nothing
render-badIndent = refl

render-dangling : layout dangling ≡ nothing
render-dangling = refl
