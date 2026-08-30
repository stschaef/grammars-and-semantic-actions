{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The internal existential: configurations, dual to parsers.

   `Core`'s parser quantifies over its continuation *inside* the DSL --
   `&ᴰ` is a grammar former, so `Parser ... : TheoryTy` and a parser is a
   first-class grammar.  The automaton layer quantifies over its carrier
   *outside*: `record NFA where field Q : FinSet ...` is a metalanguage
   record, so an automaton is not a grammar and cannot appear under `⊗`, be
   chosen by `⊕ᴰ-elim`, or be the answer of another parse.

   This file supplies the missing internal `∃`.  In linear logic the dual of
   `∀X. A X ⊸ B X` is `∃X. A X ⊗ (B X)^⊥`, so opposite `Parser` sits

     Config = ⊕[ K ] ( an answer at K , and what to do with the result )

   -- a state, an answer at that state, and a continuation.  That is an
   automaton *configuration*, and `⊕ᴰ` puts the existential inside the DSL
   exactly as `&ᴰ` puts the universal there.

   The payoff is `cut`: a parser and a configuration annihilate to the goal.
   `Parser` says "for every environment I can extend it"; `Config` says
   "here is one environment"; the cut is the only thing you can do with
   both, and it is `runP` in general form -- `runFromInit` below shows the
   ordinary runner *is* a cut against the trivial configuration. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Machine
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  where

open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Combinator.Core Alphabet _≟_
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (&⊕ᴰ-distR)

private variable ℓA ℓD ℓG : Level

module Config (𝒯 : AnswerFunctor) {ℓG' : Level} (Goal : TheorySet ℓG' tt) where
  open AnswerFunctor 𝒯 public
  open Combinators 𝒯 public using (Parser ; ParserSet ; mkP ; pAt)

  -- THE INTERNAL EXISTENTIAL.  Compare `Parser`, which is the same shape
  -- with `&ᴰ` for `⊕ᴰ` and `⇒` where the continuation sits.
  Config : (ℓK : Level) → ParserTag → ParserTag → TheorySet ℓA tt → TheoryTy _ tt
  Config ℓK a c A =
    ⊕[ K ∈ TheorySet ℓK tt ]
      (ty (▷? a (Ans K)) & (ty (▷? c (Ans (A ⊗Set K))) ⇒ ty Goal))

  -- ...and a configuration is built by naming the state.  Unlike an `NFA`
  -- record this is a ⊢-term into a grammar: `σ⊕` is the internal ∃-intro.
  atState : {ℓK : Level} {a c : ParserTag} {A : TheorySet ℓA tt}
    {D : TheoryTy ℓD tt} (K : TheorySet ℓK tt)
    (seed : D ⊢ ty (▷? a (Ans K)))
    (cont : D & ty (▷? c (Ans (A ⊗Set K))) ⊢ ty Goal)
    → D ⊢ Config ℓK a c A
  atState K seed cont = σ⊕ K ∘⊢ (seed ,& ⇒-intro cont)

  -- THE CUT.  A parser and a configuration annihilate.  This is the only
  -- term that uses both, and it is where the two quantifiers meet: `⊕ᴰ-elim`
  -- opens the existential, `π K` instantiates the universal at the very `K`
  -- it produced.
  cut : {ℓK : Level} {a c : ParserTag} {A : TheorySet ℓA tt}
    → Parser ℓK a c A & Config ℓK a c A ⊢ ty Goal
  cut {A = A} =
    ⊕ᴰ-elim (λ K →
      ⇒-app ∘⊢ ((π₂ ∘⊢ π₂) ,& (⇒-app ∘⊢ ((π K ∘⊢ π₁) ,& (π₁ ∘⊢ π₂)))))
    ∘⊢ &⊕ᴰ-distR

  -- PUSHING AN OBLIGATION.  A context expecting `A` then `B`, given a parser
  -- for `B`, is a context expecting just `A` -- with `B` moved onto the
  -- pending continuation.  `K` becomes `B ⊗Set K`, which is the push; the
  -- reassociation `⊗-assoc≅` is the only other thing it needs.  This is the
  -- configuration-side dual of `seq`.
  push : {ℓK ℓB ℓE : Level} {A : TheorySet ℓA tt} {B : TheorySet ℓB tt}
    {D : TheoryTy ℓD tt} {E : TheoryTy ℓE tt}
    (q : E ⊢ Parser ℓK ⟨□⟩ ⟨□⟩ B)
    (cfg : D ⊢ Config ℓK ⟨□⟩ ⟨□⟩ (A ⊗Set B))
    → E & D ⊢ Config (ℓ-max ℓM (ℓ-max ℓB ℓK)) ⟨□⟩ ⟨□⟩ A
  push {A = A} {B = B} q cfg =
    ⊕ᴰ-elim (λ K₀ →
      atState (B ⊗Set K₀)
        (pAt q K₀ ∘⊢ (π₁ ,& (π₁ ∘⊢ π₂)))
        (⇒-app ∘⊢ ((π₂ ∘⊢ π₂ ∘⊢ π₁) ,& (▷map {t = ⟨□⟩} (Ans-≅ ⊗-assoc≅) ∘⊢ π₂))))
    ∘⊢ &⊕ᴰ-distR ∘⊢ (π₁ ,& (cfg ∘⊢ π₂))

-- THE ORDINARY RUNNER IS A CUT.  `Core`'s `runP` instantiates the parser at
-- the unit continuation, feeds it `Ans-ε`, and unitors the result.  Those
-- three steps are exactly a configuration: state `ε↑Set`, seed `□Ans-ε`,
-- continuation "unitor, then that is the goal".  So `runP` is not a
-- primitive -- it is `cut` against the trivial configuration, and the goal
-- object is what it returns.
module Runner (𝒯 : AnswerFunctor) {ℓK : Level} {A : TheorySet ℓA tt} where
  open AnswerFunctor 𝒯
  open Combinators 𝒯 using (runP ; □Ans-ε)
  open Config 𝒯 (Ans A) using (Config ; atState ; cut ; push) public

  initial : ⊤Ty ⊢ Config (ℓ-max ℓM ℓK) ⟨□⟩ ⟨□⟩ A
  initial = atState (ε↑Set ℓK) □Ans-ε (Ans-≅ ⊗ε↑-unit-r≅ ∘⊢ □here ∘⊢ π₂)

  runByCut : ⊤Ty ⊢ Combinators.Parser 𝒯 (ℓ-max ℓM ℓK) ⟨□⟩ ⟨□⟩ A → ⊤Ty ⊢ ty (Ans A)
  runByCut p = cut ∘⊢ (p ,& initial)

  -- ...and it is the same term, on the nose.
  runByCut≡runP : (p : ⊤Ty ⊢ Combinators.Parser 𝒯 (ℓ-max ℓM ℓK) ⟨□⟩ ⟨□⟩ A)
    → runByCut p ≡ runP ℓK p
  runByCut≡runP p = refl
