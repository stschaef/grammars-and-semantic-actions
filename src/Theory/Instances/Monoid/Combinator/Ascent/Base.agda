{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Bottom-up mirror of `Combinator/Core`: polymorphic in the stack (`B ⟜ -`,
   answer at `- ⊸ Goal`) instead of the continuation.
   shift is `tok`, reduce is `mapP`, goto is `seq`, accept is `runP`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isSetΠ)
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Ascent.Base
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  where

open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.List using ([] ; _++_)

open import Theory.Instances.Monoid.Combinator.Core Alphabet _≟_ public
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using ( _⟜_ ; ⟜-intro ; ⟜-precomp ; ⟜-curry ; ⟜-unitr
        ; ⊗ε-unit-r ; ⊗ε-unit-l ; &⊕ᴰ-distR
        ; _⊸_ ; ⊸-lam ; ⊸-precomp ; ⊸-unitl ; ⊸⟜-swap )

private variable ℓA ℓB ℓC ℓD ℓG : Level

_⟜Set_ : TheorySet ℓA tt → TheorySet ℓB tt → TheorySet _ tt
(C ⟜Set B) = (ty C ⟜ ty B) , λ m → isSetΠ λ r → isSetΠ λ _ → C .snd _

_⊸Set_ : TheorySet ℓA tt → TheorySet ℓB tt → TheorySet _ tt
(A ⊸Set C) = (ty A ⊸ ty C) , λ m → isSetΠ λ l → isSetΠ λ _ → C .snd _

infixl 12 _⟜Set_
infixr 12 _⊸Set_

module Ascent (𝒯 : AnswerFunctor) {ℓG : Level} (Goal : TheorySet ℓG tt) where
  open AnswerFunctor 𝒯 public
  open Combinators 𝒯 public using (▷Ans-⊕&)

  Owes : TheorySet ℓB tt → TheorySet _ tt
  Owes B = B ⊸Set Goal

  Asc : (ℓB : Level) → ParserTag → ParserTag → TheorySet ℓA tt → TheoryTy _ tt
  Asc ℓB a c A =
    &[ B ∈ TheorySet ℓB tt ]
      (ty (▷? a (Ans (Owes B))) ⇒ ty (▷? c (Ans (Owes (B ⟜Set A)))))

  mkA : {ℓB : Level} {a c : ParserTag} {A : TheorySet ℓA tt}
    {D : TheoryTy ℓD tt}
    → (∀ (B : TheorySet ℓB tt)
        → D & ty (▷? a (Ans (Owes B))) ⊢ ty (▷? c (Ans (Owes (B ⟜Set A)))))
    → D ⊢ Asc ℓB a c A
  mkA f = &ᴰ-intro λ B → ⇒-intro (f B)

  aAt : {ℓB : Level} {a c : ParserTag} {A : TheorySet ℓA tt}
    {D : TheoryTy ℓD tt}
    → D ⊢ Asc ℓB a c A → (B : TheorySet ℓB tt)
    → D & ty (▷? a (Ans (Owes B))) ⊢ ty (▷? c (Ans (Owes (B ⟜Set A))))
  aAt p B = ⇒-app ∘⊢ ((π B ∘⊢ p) ,&p id⊢)

-- `⟜`/`⊸` are negative, so a shift has no converse: `Dec` (which transports
-- refutations backwards) does not instantiate; `Maybe` and `ND` do.
module CovAscent (𝒯 : AnswerFunctor) (cov : CovariantAnswer 𝒯)
  {ℓG : Level} (Goal : TheorySet ℓG tt) where
  open Ascent 𝒯 Goal public
  open CovariantAnswer cov public

  private variable ℓ' : Level

  -- SHIFT: `⊸⟜-swap` moves the token onto the stack.
  shift : {ℓB : Level} (c : Alphabet) {D : TheoryTy ℓD tt}
    → D ⊢ Asc ℓB ⟨▷⟩ ⟨□⟩ (litSet c)
  shift c = mkA λ B →
    ▷□ (Ans-map (⊸⟜-swap {A = literal c} {B = ty B} {C = ty Goal})
        ∘⊢ Ans-lit c) ∘⊢ π₂

  -- REDUCE: `⟜-precomp` moves the dot.
  reduce : {ℓB : Level} {a c : ParserTag}
    {β : TheorySet ℓA tt} {A : TheorySet ℓ' tt}
    → ty β ⊢ ty A → Asc ℓB a c β ⊢ Asc ℓB a c A
  reduce {c = c} {β = β} {A = A} p = mkA λ B →
    ▷map {t = c} (Ans-map (⊸-precomp {A = ty B ⟜ ty β} {A' = ty B ⟜ ty A} {C = ty Goal}
                    (⟜-precomp {B = ty A} {B' = ty β} {C = ty B} p)))
    ∘⊢ aAt id⊢ B

-- Empty stack owes the goal and delivers it; no separate soundness statement
-- since the states *are* grammars.
module _ {ℓG : Level} {Goal : TheorySet ℓG tt} where

  emptyStack : εTy ⊢ ty Goal ⟜ ty Goal
  emptyStack = ⟜-intro ⊗ε-unit-l

  start : (ty Goal ⟜ ty Goal) ⊸ ty Goal ⊢ ty Goal
  start = ⊸-unitl emptyStack

module Goto (𝒯 : AnswerFunctor) (cov : CovariantAnswer 𝒯)
  {ℓG : Level} (Goal : TheorySet ℓG tt) where
  open CovAscent 𝒯 cov Goal public

  private variable ℓ' : Level

  -- GOTO: run the later factor first, then reassociate the tower.
  goto : {ℓB : Level} {a b c : ParserTag} {D : TheoryTy ℓD tt}
    {A : TheorySet ℓA tt} (A' : TheorySet ℓ' tt)
    → D ⊢ Asc (ℓ-max ℓAlph (ℓ-max ℓB ℓ')) b c A
    → D ⊢ Asc ℓB a b A'
    → D ⊢ Asc ℓB a c (A ⊗Set A')
  goto {c = c} {A = A} A' p q = mkA λ B →
    ▷map {t = c} (Ans-map
           (⊸-precomp {A = (ty B ⟜ ty A') ⟜ ty A}
                      {A' = ty B ⟜ (ty A ⊗ ty A')} {C = ty Goal}
             (⟜-curry {A = ty A} {B = ty A'} {C = ty B})))
    ∘⊢ aAt p (B ⟜Set A') ∘⊢ (π₁ ,& aAt q B)

  -- CHOICE: injecting into a sum *is* a reduction (`reduce inl`).
  pick : {ℓB : Level} {a c : ParserTag} {A : TheorySet ℓA tt}
    {D : TheoryTy ℓD tt}
    → D ⊢ Asc ℓB a c A → D ⊢ Asc ℓB a c A → D ⊢ Asc ℓB a c A
  pick {c = c} {A = A} p q = mkA λ B →
    ▷map {t = c} (Ans-map (⊕-elim id⊢ id⊢)) ∘⊢ ▷Ans-⊕& ∘⊢ (aAt p B ,& aAt q B)

  infixr 15 _<|>_
  _<|>_ : {ℓB : Level} {a c : ParserTag}
    {A : TheorySet ℓA tt} {A' : TheorySet ℓ' tt} {D : TheoryTy ℓD tt}
    → D ⊢ Asc ℓB a c A → D ⊢ Asc ℓB a c A' → D ⊢ Asc ℓB a c (A ⊕Set A')
  p <|> q = pick (reduce inl ∘⊢ p) (reduce inr ∘⊢ q)

  idOwes : {ℓ' : Level} {A : TheorySet ℓ' tt} → εTy ⊢ ty (A ⊸Set A)
  idOwes {A = A} = ⊸-lam {A = ty A} {B = εTy} {C = ty A} ⊗ε-unit-r

  -- ACCEPT: feed the empty stack, `start`.
  runA : ⊤Ty ⊢ Asc ℓG ⟨□⟩ ⟨□⟩ Goal → ⊤Ty ⊢ ty (Ans Goal)
  runA p =
    Ans-map (start {Goal = Goal}) ∘⊢ □here ∘⊢ aAt p Goal
    ∘⊢ (id⊢ ,& ▷next {t = ⟨□⟩} (Ans-map idOwes ∘⊢ Ans-ε))

  AscSet : (ℓB : Level) (a c : ParserTag) → TheorySet ℓA tt → TheorySet _ tt
  AscSet ℓB a c A =
    Asc ℓB a c A
    , isSet&ᴰ λ B → isSet⇒ (▷? c (Ans (Owes (B ⟜Set A))) .snd)

  aApp : {ℓB : Level} {A : TheorySet ℓA tt} (B : TheorySet ℓB tt)
    → ty (▷ (AscSet ℓB ⟨□⟩ ⟨□⟩ A)) & ty (▷ (Ans (Owes B)))
    ⊢ ty (▷ (Ans (Owes (B ⟜Set A))))
  aApp B = ▷map (□here ∘⊢ aAt id⊢ B) ∘⊢ ▷lax ∘⊢ (id⊢ ,&p ▷δ□)

  module AFix (ℓB : Level) (A : TheorySet ℓA tt) where
    call : ty (▷ (AscSet ℓB ⟨□⟩ ⟨□⟩ A)) ⊢ Asc ℓB ⟨▷⟩ ⟨▷⟩ A
    call = mkA aApp

    fix : ty (▷ (AscSet ℓB ⟨□⟩ ⟨□⟩ A)) ⊢ Asc ℓB ⟨□⟩ ⟨□⟩ A
        → ⊤Ty ⊢ Asc ℓB ⟨□⟩ ⟨□⟩ A
    fix = löbG {A = AscSet ℓB ⟨□⟩ ⟨□⟩ A}

  amore : {ℓB : Level} {c : ParserTag} {A : TheorySet ℓA tt}
    → Asc ℓB ⟨▷⟩ c A ⊢ Asc ℓB ⟨□⟩ c A
  amore = mkA λ B → aAt id⊢ B ∘⊢ (id⊢ ,&p ▷wk)

  aless : {ℓB : Level} {a : ParserTag} {A : TheorySet ℓA tt}
    → Asc ℓB a ⟨□⟩ A ⊢ Asc ℓB a ⟨▷⟩ A
  aless = mkA λ B → ▷wk ∘⊢ aAt id⊢ B

  -- ACCEPT-ε: `B ⟜ ε` is `B`.
  nil : {ℓB : Level} {D : TheoryTy ℓD tt} → D ⊢ Asc ℓB ⟨□⟩ ⟨□⟩ εSet
  nil {ℓB = ℓB} = mkA λ B →
    ▷map {t = ⟨□⟩}
      (Ans-map (⊸-precomp {A = ty B} {A' = ty B ⟜ εTy} {C = ty Goal} ⟜-unitr))
    ∘⊢ π₂

  module AFixAll {ℓX ℓA'} (ℓB : Level) {X : Type ℓX}
    (A : X → TheorySet ℓA' tt) where

    Aall : TheorySet _ tt
    Aall = &ᴰSet (λ x → AscSet ℓB ⟨□⟩ ⟨□⟩ (A x))

    callAt : (x : X) → ty (▷ Aall) ⊢ Asc ℓB ⟨▷⟩ ⟨▷⟩ (A x)
    callAt x = mkA aApp ∘⊢ ▷map {t = ⟨▷⟩} (π x)

    parsers : ty (▷ Aall) ⊢ ty Aall → ⊤Ty ⊢ ty Aall
    parsers = löbG {A = Aall}

    ascAt : (ty (▷ Aall) ⊢ ty Aall) → (x : X) → ⊤Ty ⊢ Asc ℓB ⟨□⟩ ⟨□⟩ (A x)
    ascAt step x = π x ∘⊢ parsers step

  ⊥Set↑ : (ℓ' : Level) → TheorySet ℓ' tt
  ⊥Set↑ ℓ' = LiftTheoryTy ℓ' ⊥Ty , isSetLiftTheoryTy isSet⊥Ty

  failA : {ℓ' ℓB : Level} {a c : ParserTag} {D : TheoryTy ℓD tt}
    → D ⊢ Asc ℓB a c (⊥Set↑ ℓ')
  failA {c = c} = mkA λ B → ▷next {t = c} Ans-empty

  -- LOOKAHEAD: alternatives indexed by the cover, so exactly one is demanded
  -- and committed to (unlike `_<|>_`).  `altDisjoint` is the LR condition:
  -- branches at different classes cannot both match.
  module Predict {ℓC : Level} (C : M₁ → TheorySet ℓC tt)
    (lead : (o : M₁) → ty (C o) ⊗ ⊤Ty ⊢ Λ₁ o) where

    isSetM₁' : isSet M₁
    isSetM₁' = DiscreteEq→isSet _≟M_

    Alt : TheorySet _ tt
    Alt = ⊕ᴰSet isSetM₁' C

    altDisjoint : (o o' : M₁) → (o Eq.≡ o' → Empty.⊥)
      → ty (C o) & ty (C o') ⊢ ⊥Ty
    altDisjoint o o' ne =
      Λ-disjoint o o' ne
      ∘⊢ ((lead o ∘⊢ ⊗-unit-r⁻) ,&p (lead o' ∘⊢ ⊗-unit-r⁻))

    private
      commitA : {ℓB : Level} (B : TheorySet ℓB tt)
        → ty (&ᴰSet (λ o → Ans (Owes (B ⟜Set C o))))
        ⊢ ty (Ans (Owes (B ⟜Set Alt)))
      commitA B =
        ⊕ᴰ-elim atClass ∘⊢ &⊕ᴰ-distR ∘⊢ (id⊢ ,& (Λ-total ∘⊢ ⊤Ty-intro))
        where
        atClass : (o : M₁)
          → ty (&ᴰSet (λ o' → Ans (Owes (B ⟜Set C o')))) & Λ₁ o
          ⊢ ty (Ans (Owes (B ⟜Set Alt)))
        atClass o =
          Ans-map (⊸-precomp {A = ty B ⟜ ty (C o)} {A' = ty B ⟜ ty Alt}
                             {C = ty Goal}
                    (⟜-precomp {B = ty Alt} {B' = ty (C o)} {C = ty B}
                      (σ⊕ o)))
          ∘⊢ π o ∘⊢ π₁

    chooseA : {ℓB : Level} {a c : ParserTag} {D : TheoryTy ℓD tt}
      → ((o : M₁) → D ⊢ Asc ℓB a c (C o)) → D ⊢ Asc ℓB a c Alt
    chooseA {c = c} p = mkA λ B →
      ▷map {t = c} (commitA B)
      ∘⊢ ▷laxᴰ (λ o → Ans (Owes (B ⟜Set C o)))
      ∘⊢ (&ᴰ-intro λ o → aAt (p o) B)
