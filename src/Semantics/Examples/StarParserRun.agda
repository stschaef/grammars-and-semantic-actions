{-# OPTIONS --lossy-unification #-}
{- Running the parser.

   Instantiating the "just sets" elaboration at a two-letter alphabet
   gives an ordinary Agda function, so the parser computes: the
   examples below are checked by `refl`.
-}
module Semantics.Examples.StarParserRun where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool using (Bool; true; false; isSetBool)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Semantics.Signature using (DiscreteBool)
import Semantics.Examples.StarParserDemo as D

-- Alphabet {true, false}; we parse runs of `true`.
TwoLetter : hSet ℓ-zero
TwoLetter = Bool , isSetBool

module Demo = D TwoLetter DiscreteBool true

-- In the sets model a character is a letter paired with its (single,
-- featureless) token.
tok : Bool → Σ[ _ ∈ Bool ] (Unit* {ℓ-zero})
tok b = b , tt*

open Demo.Set using (parse)

-- "true true" parses: the tag is `inl`, and the parse tree is a
-- two-element list of tokens.
_ : parse (tok true ∷ tok true ∷ []) .fst ≡ lift true
_ = refl

_ : parse (tok true ∷ tok true ∷ []) .snd ≡ (tt* ∷ tt* ∷ [])
_ = refl

-- The empty string parses, to the empty list.
_ : parse [] .snd ≡ []
_ = refl

-- "true false" does not: the tag is `inr`.
_ : parse (tok true ∷ tok false ∷ []) .fst ≡ lift false
_ = refl

-- Neither does "false".
_ : parse (tok false ∷ []) .fst ≡ lift false
_ = refl
