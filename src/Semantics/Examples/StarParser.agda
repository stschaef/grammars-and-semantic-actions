{-# OPTIONS --lossy-unification #-}
{- A Kleene star parser, written once for every model.

   Fix a character `c`. This parses a string of characters and either
   returns a parse of `＂ c ＂ *` — a witness that the whole input was a
   run of `c`s — or fails.

   The parser is a single `fold*` over the input `char *`. The cons case
   distributes the tensor over the sum of characters (`⊕ᴰ-distL`) so it
   can branch on which character it read, and over the sum in the
   recursive result (`⊕ᴰ-distR`) so it can propagate failure. Both
   distributors come from `Semantics.Distributivity`, which derives them
   from ⊸/⟜ being right adjoints — so this parser is built entirely out
   of universal properties and works in any model.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary.Base

open import Semantics.Model

module Semantics.Examples.StarParser {ℓ ℓ' ℓX} {Gen : hSet ℓX}
  (M : GrammarModel ℓ ℓ' ℓX Gen)
  (DiscGen : Discrete ⟨ Gen ⟩)
  where

open import Cubical.Data.Bool using (true; false)

open import Semantics.Notation M
open import Semantics.Distributivity M
open import Semantics.Inductive.Algebra M
open import Semantics.Inductive.KleeneStar M

module _ (c : ⟨ Gen ⟩) where
  private
    module SC = Star char
    module Sc = Star ＂ c ＂

  -- The parser needs the two Kleene stars to exist: the one it reads
  -- (`char *`, i.e. strings) and the one it produces.
  module _ (Ichar : InitialAlgebra SC.*Ty) (Ic : InitialAlgebra Sc.*Ty) where
    private
      module IC = SC.WithFix Ichar
      module Ic' = Sc.WithFix Ic

    -- The input: arbitrary strings.
    string : Grammar
    string = IC._*

    -- The output: a parse of c*, or failure.
    cstar : Grammar
    cstar = Ic'._*

    Result : Grammar
    Result = cstar ⊕ ⊤

    private
      -- Having read a `c`, either extend the parse or stay failed.
      keep : ＂ c ＂ ⊗ Result ⊢ Result
      keep =
        ⊕ᴰ-elim (λ where
          (lift true) → inl ∘g Ic'.CONS
          (lift false) → inr ∘g ⊤-intro)
        ∘g ⊕ᴰ-distR

      -- Branch on the character just read.
      step : ∀ (d : ⟨ Gen ⟩) → ＂ d ＂ ⊗ Result ⊢ Result
      step d with DiscGen d c
      ... | yes d≡c = subst (λ z → ＂ z ＂ ⊗ Result ⊢ Result) (sym d≡c) keep
      ... | no _ = inr ∘g ⊤-intro

      consCase : char ⊗ Result ⊢ Result
      consCase = ⊕ᴰ-elim step ∘g ⊕ᴰ-distL

      nilCase : ε ⊢ Result
      nilCase = inl ∘g Ic'.NIL

    parse : string ⊢ Result
    parse = IC.fold* nilCase consCase

    -- The two computation rules the fold satisfies, inherited from
    -- initiality of `char *`.
    parse-nil : parse ∘g IC.NIL ≡ nilCase
    parse-nil = IC.fold*-nil nilCase consCase

    parse-cons : parse ∘g IC.CONS ≡ consCase ∘g (id ,⊗ parse)
    parse-cons = IC.fold*-cons nilCase consCase
