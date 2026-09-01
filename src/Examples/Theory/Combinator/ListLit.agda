{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `list ::= '[' ( n (',' n)* )? ']'`, answer-parametric; run at `DecAnswer`
   (a decider) and at `MaybeAnswer` (sound but not complete: `nothing` is a
   refusal, not a refutation).  Both answers pass the same test vectors. -}
open import Theory.Type.SemanticAction.Testing
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Examples.Theory.Combinator.ListLit where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Maybe as M

-- three tokens: `[`, `]`, `,`, and a number `n`
data Tok : Type ℓ-zero where
  lb rb cm nm : Tok

_≟T_ : (x y : Tok) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
lb ≟T lb = Sum.inl Eq.refl
rb ≟T rb = Sum.inl Eq.refl
cm ≟T cm = Sum.inl Eq.refl
nm ≟T nm = Sum.inl Eq.refl
lb ≟T rb = Sum.inr λ ()
lb ≟T cm = Sum.inr λ ()
lb ≟T nm = Sum.inr λ ()
rb ≟T lb = Sum.inr λ ()
rb ≟T cm = Sum.inr λ ()
rb ≟T nm = Sum.inr λ ()
cm ≟T lb = Sum.inr λ ()
cm ≟T rb = Sum.inr λ ()
cm ≟T nm = Sum.inr λ ()
nm ≟T lb = Sum.inr λ ()
nm ≟T rb = Sum.inr λ ()
nm ≟T cm = Sum.inr λ ()

import Theory.Instances.Monoid.Combinator.Core Tok _≟T_ as C

module Grammar (𝒯 : C.AnswerFunctor) where
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

module AtDec where
  open import Theory.Instances.Monoid.Combinator.Decidable.Base Tok _≟T_
    (ℓ-suc ℓ-zero)
  module G = Grammar DecAnswer

  decList : Decidable _
  decList = runP G.ℓG (pmore ∘⊢ G.listP)

  ok? : String → M.Maybe Unit
  ok? = observe decList (semact-dec (semact-pure tt))

module AtMaybe where
  open import Theory.Instances.Monoid.Combinator.Incomplete.Base Tok _≟T_
    (ℓ-suc ℓ-zero)
  module G = Grammar MaybeAnswer

  testList : Test _
  testList = runP G.ℓG (pmore ∘⊢ G.listP)

  ok? : String → M.Maybe Unit
  ok? = observe testList (semact-Maybe (semact-pure tt))


goodCases badCases : List (List Tok × M.Maybe Unit)
goodCases =
    (lb ∷ rb ∷ [])                          ↦ M.just tt
  ∷ (lb ∷ nm ∷ rb ∷ [])                     ↦ M.just tt
  ∷ (lb ∷ nm ∷ cm ∷ nm ∷ rb ∷ [])           ↦ M.just tt
  ∷ (lb ∷ nm ∷ cm ∷ nm ∷ cm ∷ nm ∷ rb ∷ []) ↦ M.just tt
  ∷ []
badCases =
    (lb ∷ [])                     ↦ M.nothing
  ∷ (lb ∷ cm ∷ rb ∷ [])           ↦ M.nothing
  ∷ (lb ∷ nm ∷ cm ∷ rb ∷ [])      ↦ M.nothing
  ∷ (lb ∷ nm ∷ nm ∷ rb ∷ [])      ↦ M.nothing
  ∷ (nm ∷ [])                     ↦ M.nothing
  ∷ []

decAccepts : passes (AtDec.ok? at goodCases)
decAccepts = refl

decRejects : passes (AtDec.ok? at badCases)
decRejects = refl

maybeAccepts : passes (AtMaybe.ok? at goodCases)
maybeAccepts = refl

maybeRejects : passes (AtMaybe.ok? at badCases)
maybeRejects = refl
