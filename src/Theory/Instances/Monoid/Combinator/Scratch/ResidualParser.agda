{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- SCRATCH.  The parser motive with the internal hom `⊸` (and its mirror
   `⟜`) in place of the pointwise `⇒`.  Nothing here is imported by the
   library. -}
open import Cubical.Foundations.Prelude
open import Cubical.WildCat.LocallySmall.Base
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Scratch.ResidualParser
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  where

open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)

open import Theory.Instances.Monoid.Combinator.Core Alphabet _≟_ public
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using ( _⊸_ ; ⊸-lam ; ⊸-lam⁻ ; ⊸-app ; ⊸-precomp ; ⊸-post
        ; ⊸-curry ; ⊸-uncurry ; ⊸-unitl
        ; _⟜_ ; ⟜-intro ; ⟜-intro⁻ ; ⟜-app ; ⟜-precomp ; ⟜-post
        ; ⟜-curry ; ⟜-curry⁻ ; ⟜-uncurry ; ⟜-unitr ; ⟜-unitr⁻
        ; ⊗ε-unit-l ; ⊗ε-unit-l⁻ ; ⊗ε-unit-r ; ⊗ε-unit-r⁻ ; castEq )

open WildCatNotation
open WildCatIso

private variable ℓA ℓB ℓC ℓD ℓK ℓL : Level

module R (𝒯 : AnswerFunctor) where
  open Combinators 𝒯 public

  -- The experiment's motive: the pointwise `⇒` of `Parser` replaced by the
  -- genuine internal hom.
  Parser' : (ℓK : Level) → ParserTag → ParserTag → TheorySet ℓA tt
    → TheoryTy _ tt
  Parser' ℓK a c A =
    &[ K ∈ TheorySet ℓK tt ]
      (ty (▷? a (Ans K)) ⊸ ty (▷? c (Ans (A ⊗Set K))))

  -- 1. `nil'`.  Under `⇒` this was `⊤Ty ⊢ Parser ...`: a parser for `ε` may
  -- be built from nothing.  Under `⊸` the parser sits *at its own index*, so
  -- the only way to answer at `l ++ m` from an answer at `l` is `m ≡ []`:
  -- the hypothesis has to be `εTy`.
  nil' : {ℓK : Level} {a : ParserTag} → εTy ⊢ Parser' ℓK a a εSet
  nil' {ℓK = ℓK} {a = a} m u K l x = go m (u .snd .fst) l x
    where
    go : (w : ↓M tt) → [] Eq.≡ w → (l : ↓M tt)
       → ty (▷? a (Ans K)) l → ty (▷? a (Ans (εSet ⊗Set K))) (l ++ w)
    go .[] Eq.refl l y =
      castEq {A = λ z → ty (▷? a (Ans (εSet ⊗Set K))) z}
        (Eq.sym (++-unit-rEq l)) (▷Ans-≅ ⊗ε-unit-l≅ l y)

  -- 5. `runP'`.  Unharmed: `⊸-unitl` feeds the left slot at the unit, and
  -- `[] ++ m` is `m` on the nose.
  runP' : (ℓK : Level) {A : TheorySet ℓA tt}
    → Parser' (ℓ-max ℓM ℓK) ⟨□⟩ ⟨□⟩ A ⊢ ty (Ans A)
  runP' ℓK m p =
    Ans-≅ ⊗ε↑-unit-r≅ m
      (□here m (p (ε↑Set ℓK) [] (□Ans-ε {D = εTy} [] εTy-pt)))

module Rcov (𝒯 : AnswerFunctor) (cov : CovariantAnswer 𝒯) where
  open R 𝒯 public
  open CovariantAnswer cov public

  -- 3. `mapP'`.  Also unharmed: it only post-composes on the conclusion,
  -- and post-composition does not touch the index.
  mapP' : {ℓK : Level} {a c : ParserTag}
    {A : TheorySet ℓA tt} {B : TheorySet ℓB tt}
    → ty A ⊢ ty B → Parser' ℓK a c A ⊢ Parser' ℓK a c B
  mapP' f m p K l x = ▷map (Ans-map (f ,⊗ id⊢)) (l ++ m) (p K l x)

-- ---------------------------------------------------------------------
-- The mirror motive, with `⟜` and the answer's factors in the order the
-- library already uses.  This is the variant the combinators survive.

-- What `Ans-lit` becomes once the parser no longer has to *find* the
-- split: a plain strength.  Not derivable from `AnswerFunctor`, but every
-- concrete answer has it.
record StrongAnswer (𝒯 : AnswerFunctor) : Typeω where
  open AnswerFunctor 𝒯
  field
    Ans-⊗l : {ℓA ℓK : Level} {A : TheorySet ℓA tt} {K : TheorySet ℓK tt}
      → ty A ⊗ ty (Ans K) ⊢ ty (Ans (A ⊗Set K))

module R⟜ (𝒯 : AnswerFunctor) where
  open Combinators 𝒯 public

  -- A parser is now a *grammar*: `Parser⟜ ℓK A` at `m` says that `m`,
  -- extended on the right by any `K`-string, yields an `A ⊗ K` answer.
  Parser⟜ : (ℓK : Level) → TheorySet ℓA tt → TheoryTy _ tt
  Parser⟜ ℓK A =
    &[ K ∈ TheorySet ℓK tt ] (ty (Ans (A ⊗Set K)) ⟜ ty (Ans K))

  -- intro/elim are literally the residual adjunction
  mkP⟜ : {ℓK : Level} {A : TheorySet ℓA tt} {D : TheoryTy ℓD tt}
    → ((K : TheorySet ℓK tt) → D ⊗ ty (Ans K) ⊢ ty (Ans (A ⊗Set K)))
    → D ⊢ Parser⟜ ℓK A
  mkP⟜ f = &ᴰ-intro λ K → ⟜-intro (f K)

  pAt⟜ : {ℓK : Level} {A : TheorySet ℓA tt} {D : TheoryTy ℓD tt}
    → D ⊢ Parser⟜ ℓK A → (K : TheorySet ℓK tt)
    → D ⊗ ty (Ans K) ⊢ ty (Ans (A ⊗Set K))
  pAt⟜ p K = ⟜-app ∘⊢ ((π K ∘⊢ p) ,⊗ id⊢)

  -- 1'. `nil⟜`
  nil⟜ : {ℓK : Level} → εTy ⊢ Parser⟜ ℓK εSet
  nil⟜ = mkP⟜ λ K → Ans-≅ ⊗ε-unit-l≅ ∘⊢ ⊗ε-unit-l

  -- the choice combinator still duplicates: `&` is cartesian even though
  -- `⊗` is not, so the same `D ⊗ Ans K` may be fed to both branches
  infixr 15 _<|>⟜_
  _<|>⟜_ : {ℓK : Level} {A : TheorySet ℓA tt} {B : TheorySet ℓB tt}
    {D : TheoryTy ℓD tt}
    → D ⊢ Parser⟜ ℓK A → D ⊢ Parser⟜ ℓK B → D ⊢ Parser⟜ ℓK (A ⊕Set B)
  (p <|>⟜ q) = mkP⟜ λ K →
    Ans-≅ ⊗⊕-distL≅ ∘⊢ Ans-⊕& ∘⊢ (pAt⟜ p K ,& pAt⟜ q K)

  -- 4'. `seq⟜`.  The hypotheses are *tensored*, not shared: two sequenced
  -- parsers occupy two different pieces of the input.
  seq⟜ : {ℓK ℓB : Level} {A : TheorySet ℓA tt}
    {D : TheoryTy ℓD tt} {E : TheoryTy ℓC tt} (B : TheorySet ℓB tt)
    → D ⊢ Parser⟜ (ℓ⊗ ℓB ℓK) A → E ⊢ Parser⟜ ℓK B
    → D ⊗ E ⊢ Parser⟜ ℓK (A ⊗Set B)
  seq⟜ B p q = mkP⟜ λ K →
    Ans-≅ ⊗-assoc≅ ∘⊢ pAt⟜ p (B ⊗Set K) ∘⊢ (id⊢ ,⊗ pAt⟜ q K) ∘⊢ ⊗-assoc

  -- 5'. `runP⟜`: instantiating at the unit is `⟜-unitr`, and the result is
  -- an answer *at the parser's own index* -- the parser is a subformula.
  runP⟜ : (ℓK : Level) {A : TheorySet ℓA tt}
    → Parser⟜ (ℓ-max ℓM ℓK) A ⊢ ty (Ans A)
  runP⟜ ℓK {A = A} =
    Ans-≅ ⊗ε↑-unit-r≅
    ∘⊢ ⟜-unitr
    ∘⊢ ⟜-precomp (Ans-≅ lift≅ ∘⊢ Ans-ε ∘⊢ ⊤Ty-intro)
    ∘⊢ π (ε↑Set ℓK)

module R⟜str (𝒯 : AnswerFunctor) (str : StrongAnswer 𝒯) where
  open R⟜ 𝒯 public
  open StrongAnswer str public

  -- 2'. `tok⟜`: no lookahead, no guarded payment.  The split is not
  -- searched for -- it is the parser's own index.
  tok⟜ : {ℓK : Level} (c : Alphabet) → literal c ⊢ Parser⟜ ℓK (litSet c)
  tok⟜ c = mkP⟜ λ K → Ans-⊗l

  anyTok⟜ : {ℓK : Level} → char ⊢ Parser⟜ ℓK charSet
  anyTok⟜ = mkP⟜ λ K → Ans-⊗l

module R⟜cov (𝒯 : AnswerFunctor) (cov : CovariantAnswer 𝒯) where
  open R⟜ 𝒯 public
  open CovariantAnswer cov public

  -- 3'. `mapP⟜`
  mapP⟜ : {ℓK : Level} {A : TheorySet ℓA tt} {B : TheorySet ℓB tt}
    → ty A ⊢ ty B → Parser⟜ ℓK A ⊢ Parser⟜ ℓK B
  mapP⟜ f = mkP⟜ λ K → Ans-map (f ,⊗ id⊢) ∘⊢ pAt⟜ id⊢ K

  fail⟜ : {ℓK : Level} {A : TheorySet ℓA tt} {D : TheoryTy ℓD tt}
    → D ⊢ Parser⟜ ℓK A
  fail⟜ = mkP⟜ λ K → Ans-empty ∘⊢ ⊤Ty-intro

-- ---------------------------------------------------------------------
-- At `Maybe`, end to end.

import Theory.Instances.Monoid.Combinator.Incomplete.Base
  Alphabet _≟_ ℓ-zero as Inc

MaybeStrong : StrongAnswer Inc.MaybeAnswer
MaybeStrong .StrongAnswer.Ans-⊗l = Inc.Maybe⊗r

module Demo where
  open R⟜str Inc.MaybeAnswer MaybeStrong

  -- `seq⟜` of two `tok⟜`s: the hypothesis is the *grammar* `literal c ⊗
  -- literal d`, exactly the strings this parser accepts.
  twoTok : (c d : Alphabet)
    → literal c ⊗ literal d ⊢ Parser⟜ ℓM (litSet c ⊗Set litSet d)
  twoTok c d = seq⟜ (litSet d) (tok⟜ c) (tok⟜ d)

  twoTokRun : (c d : Alphabet)
    → literal c ⊗ literal d ⊢ Maybe (literal c ⊗ literal d)
  twoTokRun c d = runP⟜ ℓM ∘⊢ twoTok c d

  -- ...and it really answers: `just`, on the nose, by computation.
  twoTok-just : (c d : Alphabet)
    → twoTokRun c d (c ∷ d ∷ [])
        (two (c ∷ []) (d ∷ []) , Eq.refl , (Eq.refl , (Eq.refl , tt*)))
      ≡ just {A = literal c ⊗ literal d} (c ∷ d ∷ [])
        (two (c ∷ []) (d ∷ []) , Eq.refl , (Eq.refl , (Eq.refl , tt*)))
  twoTok-just c d = refl
