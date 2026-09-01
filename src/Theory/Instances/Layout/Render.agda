{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Rendering is a fold of the derivation: the `Close` witness's steps ARE the
   `}`s and the `;`, so `closeOut` reads them off and nothing here compares
   two columns.  The mode-and-stack state is the index, not derivation data. -}
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

-- An ordinary external list: `Out` is not a sort, and the pass leaves the
-- theory only at `observe`.
data Out : Type ℓ-zero where
  oTok : Tok → Out
  oOpen oClose oSemi : Out

closeAll : Stack → List Out
closeAll [] = []
closeAll (_ ∷ ms) = oClose ∷ closeAll ms

closeOut : (c : ℕ) (ms : Stack) → Close c ms → List Out
closeOut c [] _ = []
closeOut c (m ∷ ms) (Sum.inl (_ , w)) = oClose ∷ closeOut c ms w
closeOut c (m ∷ ms) (Sum.inr (Sum.inl _)) = oSemi ∷ []
closeOut c (m ∷ ms) (Sum.inr (Sum.inr _)) = []

-- Total on derivations; the one failing clause (an opener at the end of
-- input) is absurd.
render : (S : LState) (ts : TokList) → Layout S ts → List Out
render (scanning , ms) tnil _ = closeAll ms
render (opening , ms) tnil ()
render (scanning , ms) (tcons (k , c) ts) (w , d) =
  closeOut c ms w ++ (oTok (k , c) ∷ render (modeAfter k , popTo c ms) ts d)
render (opening , ms) (tcons (k , c) ts) (w , d) =
  oOpen ∷ oTok (k , c) ∷ render (modeAfter k , c ∷ ms) ts d

renderAction : (S : LState) → SemanticAction (Layout S) (List Out)
renderAction S ts d = render S ts d , tt

compile : LState → TokList → Maybe (List Out)
compile S = observe (CD.laidOut S) (semact-dec (renderAction S))

topLevel : LState
topLevel = scanning , []

layout : TokList → Maybe (List Out)
layout = compile topLevel
