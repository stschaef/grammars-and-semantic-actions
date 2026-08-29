{-# OPTIONS --lossy-unification #-}
{- The chart model, made concrete.

   `Semantics.Instances.Spans` reads a grammar as a matrix indexed by
   spans of positions, with ⊗ as matrix multiplication. Instantiating it
   at a fixed input word turns the model into that word's parse chart:
   the denotation of `A` at the span `i…j` is the set of parses of `A`
   over that stretch of the input.

   Below, the input is `true false` over a two-letter alphabet, and the
   grammar is `＂ true ＂ ⊗ ＂ false ＂`. Its entry at the full span
   `0…2` is inhabited — by the parse that splits at position 1 — and
   that parse is written out explicitly.
-}
module Semantics.Examples.ChartDemo where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Data.Bool using (Bool; true; false; isSetBool)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Semantics.Instances.Spans

TwoLetter : hSet ℓ-zero
TwoLetter = Bool , isSetBool

-- The input word: `true false`.
input : List Bool
input = true ∷ false ∷ []

module W = Chart TwoLetter input

open import Semantics.Notation W.chart

-- The grammar `＂ true ＂ ⊗ ＂ false ＂`.
G : Grammar
G = ＂ true ＂ ⊗ ＂ false ＂

-- Its chart entry at the whole span is inhabited: split at position 1,
-- with `true` covering 0…1 and `false` covering 1…2.
parse : ⟨ G 0 2 ⟩
parse = 1 , ((Eq.refl , Eq.refl) , (Eq.refl , Eq.refl))

-- The span really is the whole of the input.
_ : W.wholeInput ≡ 2
_ = refl
