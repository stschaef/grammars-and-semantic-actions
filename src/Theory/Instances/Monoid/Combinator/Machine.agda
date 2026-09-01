{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Configurations, dual to parsers (∃ dual to the parser's internal ∀):

     Config = ⊕[ K ] ( an answer at K , and what to do with the result )

   `cut` annihilates a parser and a configuration to the goal. -}
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
  using ()

private variable ℓA ℓD ℓG : Level

module Config (𝒯 : AnswerFunctor) {ℓG' : Level} (Goal : TheorySet ℓG' tt) where
  open AnswerFunctor 𝒯 public
  open Combinators 𝒯 public using (Parser ; ParserSet ; mkP ; pAt)

  -- same shape as `Parser` with `&ᴰ` for `⊕ᴰ` and `⇒` at the continuation
  Config : (ℓK : Level) → ParserTag → ParserTag → TheorySet ℓA tt → TheoryTy _ tt
  Config ℓK a c A =
    ⊕[ K ∈ TheorySet ℓK tt ]
      (ty (▷? a (Ans K)) & (ty (▷? c (Ans (A ⊗Set K))) ⇒ ty Goal))

  -- a ⊢-term into a grammar, not an `NFA` record: `σ⊕` is internal ∃-intro
  atState : {ℓK : Level} {a c : ParserTag} {A : TheorySet ℓA tt}
    {D : TheoryTy ℓD tt} (K : TheorySet ℓK tt)
    (seed : D ⊢ ty (▷? a (Ans K)))
    (cont : D & ty (▷? c (Ans (A ⊗Set K))) ⊢ ty Goal)
    → D ⊢ Config ℓK a c A
  atState K seed cont = σ⊕ K ∘⊢ (seed ,& ⇒-intro cont)

  -- `⊕ᴰ-elim` opens the existential; `π K` instantiates the universal at
  -- the very `K` it produced
  cut : {ℓK : Level} {a c : ParserTag} {A : TheorySet ℓA tt}
    → Parser ℓK a c A & Config ℓK a c A ⊢ ty Goal
  cut {A = A} =
    ⊕ᴰ-elim (λ K →
      ⇒-app ∘⊢ ((π₂ ∘⊢ π₂) ,& (⇒-app ∘⊢ ((π K ∘⊢ π₁) ,& (π₁ ∘⊢ π₂)))))
    ∘⊢ &⊕ᴰ-distR

  -- push: `K` becomes `B ⊗Set K`; the configuration-side dual of `seq`
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

-- `runP` is not a primitive: it is `cut` against the trivial configuration
-- (state `ε↑Set`, seed `□Ans-ε`, continuation the unitor)
module Runner (𝒯 : AnswerFunctor) {ℓK : Level} {A : TheorySet ℓA tt} where
  open AnswerFunctor 𝒯
  open Combinators 𝒯 using (runP ; □Ans-ε)
  open Config 𝒯 (Ans A) using (Config ; atState ; cut ; push) public

  initial : ⊤Ty ⊢ Config (ℓ-max ℓM ℓK) ⟨□⟩ ⟨□⟩ A
  initial = atState (ε↑Set ℓK) □Ans-ε (Ans-≅ ⊗ε↑-unit-r≅ ∘⊢ □here ∘⊢ π₂)

  runByCut : ⊤Ty ⊢ Combinators.Parser 𝒯 (ℓ-max ℓM ℓK) ⟨□⟩ ⟨□⟩ A → ⊤Ty ⊢ ty (Ans A)
  runByCut p = cut ∘⊢ (p ,& initial)

  -- the same term, on the nose
  runByCut≡runP : (p : ⊤Ty ⊢ Combinators.Parser 𝒯 (ℓ-max ℓM ℓK) ⟨□⟩ ⟨□⟩ A)
    → runByCut p ≡ runP ℓK p
  runByCut≡runP p = refl
