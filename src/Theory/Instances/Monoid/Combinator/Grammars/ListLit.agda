{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `list ::= '[' ( n (',' n)* )? ']'`, built entirely from the derived
   combinators, for every answer.

   The point of the example is what is *absent*: no `NT`, no `Tag`, no
   `body : Tag → Code`, no `isSetValued`, no roll/unroll pair.  Every other
   grammar in this directory pays that ~60 lines to get a repetition;
   `sepBy` is the whole grammar here.

   `Decidable/ListLit` and `Incomplete/ListLit` were this text twice,
   differing only in which answer they picked -- and, gratuitously, in
   whether they wrote the inferred grammar types out or left them `_`.
   Nothing in the grammar mentions an answer, so it is parametric, exactly
   as `Grammars/Dyck` is; those two modules now only choose one and run the
   tests. -}
open import Cubical.Foundations.Prelude
open import Theory.Instances.Monoid.Grammars.ListLit using (Tok ; _≟T_)
import Theory.Instances.Monoid.Combinator.Core Tok _≟T_ as C

module Theory.Instances.Monoid.Combinator.Grammars.ListLit
  (𝒯 : C.AnswerFunctor) where

open import Theory.Instances.Monoid.Grammars.ListLit public
open C public
open Combinators 𝒯 public
open import Theory.Instances.Monoid.Combinator.Syntax Tok _≟T_ 𝒯 public

ℓG : Level
ℓG = ℓ-max ℓM (ℓ-suc ℓ-zero)

-- `n (',' n)*`
items : ⊤Ty ⊢ Parser ℓG ⟨▷⟩ ⟨□⟩ _
items = sepBy ℓG (tok nm) (tok cm)

-- `'[' items? ']'`
listP : ⊤Ty ⊢ Parser ℓG ⟨▷⟩ ⟨□⟩ _
listP = between (tok lb) (box (option items)) (pless ∘⊢ tok rb)
