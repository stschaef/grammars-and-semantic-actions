{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- What proof-relevance buys here: the checker stops saying "well laid out"
   and starts emitting the braced stream.

   Layout is a tree-to-tree pass, so the interesting object is not the
   decision but the output, and the output is a fold of the derivation.
   The `Close` witness is where the content lives: its "this block closes"
   steps are the `}`s and its terminal case is the `;` or its absence, so
   `closeOut` *reads* them off in the way `Annotated/Elaborate`'s
   `deBruijn` reads an index off a `Lookup`.  Nothing here recomputes
   `popTo`, and nothing here compares two columns.

   `Layout` could have been the predicate `layoutOk S ts ≡ true`, and it
   would have been the same proposition; only this form carries what a
   compiler needs.  The mode-and-stack state, by contrast, is *not* carried
   in the derivation -- it is the index, so it is available for free at
   every recursive call, which is exactly the division of labour the
   framework is for.

   `compile` is a composition of three internal terms and one observation,
   as in `Elaborate`: the checker `⊤Ty ⊢ DecTy (Layout S)`, the action that
   `semact-dec` builds, and `observe`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Layout.Render where

open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Sum as Sum

open import Theory.Instances.Layout.Offside public

open import Theory.Type.SemanticAction.Base LEqns ⊥ noVar lPresentation
import Theory.Combinator.Answer.Decidable LEqns ⊥ noVar lPresentation as D

module CD = Check D.DecAnswer

-- The laid-out stream: the input tokens with the layout punctuation the
-- rule inserted.  It is an ordinary external list, so `Out` is not a sort
-- and the pass never leaves the theory until `observe`.
data Out : Type ℓ-zero where
  oTok : Tok → Out
  oOpen oClose oSemi : Out

-- Closing every block still open at the end of input.  The stack's length
-- is the only thing consulted, because there is no token left to compare
-- against.
closeAll : Stack → List Out
closeAll [] = []
closeAll (_ ∷ ms) = oClose ∷ closeAll ms

-- ...and the punctuation a token at column `c` induces, read off the
-- witness.  One `}` per closed block; then a `;` exactly when the
-- surviving block starts at `c`, and nothing when the token is a
-- continuation or when no block survives.
closeOut : (c : ℕ) (ms : Stack) → Close c ms → List Out
closeOut c [] _ = []
closeOut c (m ∷ ms) (Sum.inl (_ , w)) = oClose ∷ closeOut c ms w
closeOut c (m ∷ ms) (Sum.inr (Sum.inl _)) = oSemi ∷ []
closeOut c (m ∷ ms) (Sum.inr (Sum.inr _)) = []

-- The fold.  There is no failure case: a derivation is a proof the stream
-- is laid out, so rendering is total on derivations, and the one clause
-- that would fail -- an opener at the end of input -- is absurd.
render : (S : LState) (ts : TokList) → Layout S ts → List Out
render (scanning , ms) tnil _ = closeAll ms
render (opening , ms) tnil ()
render (scanning , ms) (tcons (k , c) ts) (w , d) =
  closeOut c ms w ++ (oTok (k , c) ∷ render (modeAfter k , popTo c ms) ts d)
render (opening , ms) (tcons (k , c) ts) (w , d) =
  oOpen ∷ oTok (k , c) ∷ render (modeAfter k , c ∷ ms) ts d

renderAction : (S : LState) → SemanticAction (Layout S) (List Out)
renderAction S ts d = render S ts d , tt

-- Check, then render.
compile : LState → TokList → Maybe (List Out)
compile S = observe (CD.laidOut S) (semact-dec (renderAction S))

-- The state a file starts in: nothing open, and no keyword pending.
topLevel : LState
topLevel = scanning , []

layout : TokList → Maybe (List Out)
layout = compile topLevel
