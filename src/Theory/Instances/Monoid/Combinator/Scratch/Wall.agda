{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- SCRATCH.  What the `⊸` motive of `ResidualParser.R` does and does not
   admit. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Scratch.Wall
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  where

open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.FinData using (Fin ; zero ; suc)

open import Theory.Instances.Monoid.Combinator.Scratch.ResidualParser
  Alphabet _≟_
open import Theory.Type.Later.Indexed MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (castEq ; _⟜_)

private variable ℓA ℓB ℓC ℓD ℓK : Level

module W (𝒯 : AnswerFunctor) where
  open R 𝒯

  -- 2.  The goal of `tok'`, spelled out.  The only rule that produces a
  -- token answer is `Ans-lit`, and it produces it *at the index its
  -- hypothesis already sits at*.  Writing that term gives
  --
  --   Theory/.../Wall.agda:_: error: [UnequalTerms]
  --   The terms
  --     l
  --   and
  --     l ++ m
  --   are not equal at type List Alphabet
  --   when checking that the expression ▷□ (Ans-lit c) l x has type
  --   ty (□ (Ans (litSet c ⊗Set K))) (l ++ m)
  --
  -- and no cast repairs it: `litSet c ⊗Set K` at `l ++ m` (with `m` the
  -- singleton `c`) asks for a string that *begins* with `c`, while the
  -- hypothesis is about `l`, which sits to the *left* of that `c`.
  --
  --   tok'-goal : (c : Alphabet) (K : TheorySet ℓK tt) (m : ↓M tt)
  --     → literal c m → (l : ↓M tt) → ty (▷ (Ans K)) l
  --     → ty (□ (Ans (litSet c ⊗Set K))) (l ++ m)
  --   tok'-goal c K m lc l x = ▷□ (Ans-lit c) l x

  -- 4.  `seq'` *does* compose -- but the tensor of hypotheses comes out
  -- twisted: the parser for `B` is the *left* factor and the parser for
  -- `A` the right one, while the answer is about `A ⊗ B`.  This is the
  -- same mismatch as `tok'`, now visible as a permutation rather than as
  -- a type error.
  seq' : {ℓK ℓB : Level} {a b c : ParserTag} {A : TheorySet ℓA tt}
    {D : TheoryTy ℓD tt} {E : TheoryTy ℓC tt} (B : TheorySet ℓB tt)
    → D ⊢ Parser' ℓK a b B → E ⊢ Parser' (ℓ⊗ ℓB ℓK) b c A
    → D ⊗ E ⊢ Parser' ℓK a c (A ⊗Set B)
  seq' {c = c} {A = A} {D = D} {E = E} B q p m (ms , e , (d , (ee , _))) K l x =
    go (ms zero) (ms (suc zero)) m d ee e
    where
    go : (u v w : ↓M tt) → D u → E v → (u ++ v) Eq.≡ w
       → ty (▷? c (Ans ((A ⊗Set B) ⊗Set K))) (l ++ w)
    go u v w d' e' Eq.refl =
      castEq {A = λ z → ty (▷? c (Ans ((A ⊗Set B) ⊗Set K))) z}
        (++-assocEq l u v)
        (▷Ans-≅ ⊗-assoc≅ ((l ++ u) ++ v)
          (p v e' (B ⊗Set K) (l ++ u) (q u d' K l x)))

-- ---------------------------------------------------------------------
-- Is `Parser` related to the residual motive by a `⊢`-term either way?
-- Compare at the *modality-free* pointwise motive, so that `⇒` vs `⟜` is
-- the only difference left.

module Cmp (𝒯 : AnswerFunctor) where
  open R⟜ 𝒯

  Parser⇒ : (ℓK : Level) → TheorySet ℓA tt → TheoryTy _ tt
  Parser⇒ ℓK A =
    &[ K ∈ TheorySet ℓK tt ] (ty (Ans K) ⇒ ty (Ans (A ⊗Set K)))

  -- What *is* derivable in both: the elimination.  `⇒` eliminates against
  -- `&` -- the parser and its continuation are about the *same* string --
  -- and `⟜` against `⊗` -- they are about *adjacent* ones.  That is the
  -- whole difference.
  app⇒ : {ℓK : Level} {A : TheorySet ℓA tt} (K : TheorySet ℓK tt)
    → Parser⇒ ℓK A & ty (Ans K) ⊢ ty (Ans (A ⊗Set K))
  app⇒ K = ⇒-app ∘⊢ (π K ,&p id⊢)

  app⟜ : {ℓK : Level} {A : TheorySet ℓA tt} (K : TheorySet ℓK tt)
    → Parser⟜ ℓK A ⊗ ty (Ans K) ⊢ ty (Ans (A ⊗Set K))
  app⟜ K = pAt⟜ id⊢ K


  -- Neither direction is a `⊢`-term.  Both attempts are the only ones
  -- there are -- there is nothing else to feed the continuation to --
  -- and both are rejected on the index:
  --
  --   fwd : Parser⟜ ℓK A ⊢ Parser⇒ ℓK A
  --   fwd m p K x = p K m x
  --     error: [UnequalTerms] The terms `m ++ m` and `m` are not equal
  --     at type List Alphabet, when checking that the expression
  --     `p K m x` has type `ty (Ans (A ⊗Set K)) m`
  --
  --   bwd : Parser⇒ ℓK A ⊢ Parser⟜ ℓK A
  --   bwd m p K r x = p K x
  --     error: [UnequalTerms] The terms `r` and `m` are not equal at
  --     type (List Alphabet), when checking that the expression `x` has
  --     type `ty (Ans K) m`

  -- The one bridge that does exist: at the unit the residual *is* the
  -- pointwise implication.  Nowhere else.
  atε : {ℓK : Level} {A : TheorySet ℓA tt}
    → Parser⟜ ℓK A & εTy ⊢ Parser⇒ ℓK A
  atε {A = A} m (p , u) K = go m (u .snd .fst) p
    where
    go : (w : ↓M tt) → [] Eq.≡ w → Parser⟜ _ A w
       → (ty (Ans K) ⇒ ty (Ans (A ⊗Set K))) w
    go .[] Eq.refl p' x = p' K [] x

-- ---------------------------------------------------------------------
-- Why the guarded modality had to be dropped from the residual motive.

module Guard (𝒯 : AnswerFunctor) where
  open R⟜ 𝒯

  Parser⟜▷ : (ℓK : Level) → ParserTag → ParserTag → TheorySet ℓA tt
    → TheoryTy _ tt
  Parser⟜▷ ℓK a c A =
    &[ K ∈ TheorySet ℓK tt ]
      (ty (▷? c (Ans (A ⊗Set K))) ⟜ ty (▷? a (Ans K)))


  -- `Ans-lit` is the only rule that produces a token answer, and it wants
  -- its hypothesis at the index it answers at.  Under `⟜` that index has
  -- moved:
  --
  --   tok⟜▷-goal : (c : Alphabet) (K : TheorySet ℓK tt) (m : ↓M tt)
  --     → literal c m → (r : ↓M tt) → ty (▷ (Ans K)) r
  --     → ty (□ (Ans (litSet c ⊗Set K))) (m ++ r)
  --   tok⟜▷-goal c K m lc r x = ▷□ (Ans-lit c) r x
  --
  --     error: [UnequalTerms] The terms `r` and `m ++ r` are not equal at
  --     type List Alphabet, when checking that the expression
  --     `▷□ (Ans-lit c) r x` has type
  --     `ty (□ (Ans (litSet c ⊗Set K))) (m ++ r)`
  --
  -- The rule that would repair the *hypothesis* side is `▷cons` below:
  -- the suffix order is generated by `∷`, so what holds at `r` and below
  -- holds at every proper suffix of `c ∷ r`.  It is true, but it is not
  -- in `Suffix/Base`'s interface -- every rule there keeps the index
  -- fixed -- so it has to be built from the `Later.Indexed` internals.

-- the missing structural rule, built by hand
private
  module G = GuardedIndexed {X = Unit} (λ _ → tt) suffixOrder

  fam : TheorySet ℓA tt → G.SetFam ℓA
  fam A = (λ _ → ty A) , λ _ → A .snd

▷cons : {A : TheorySet ℓA tt} (c : Alphabet) (r : ↓M tt)
  → ty (□ A) r → ty (▷ A) (c ∷ r)
▷cons {A = A} c r p = G.Fam▷.▷intro (fam A .fst) (fam A .snd) go
  where
  go : (x' : Unit) (m' : ↓M tt) → m' ◂ (c ∷ r) → ty A m'
  go tt m' (Sum.inl Eq.refl) = p .fst
  go tt m' (Sum.inr i) = G.▷app (fam A) i (p .snd)

module Guard' (𝒯 : AnswerFunctor) where
  open R⟜ 𝒯

  -- ...and with it the token rule does go through -- but only with the
  -- *conclusion's* modality dropped, so it can no longer be fed to
  -- another parser's hypothesis, and `seq⟜` does not compose.
  tok⟜▷ : (c : Alphabet) (K : TheorySet ℓK tt) (m : ↓M tt) → literal c m
    → (r : ↓M tt) → ty (□ (Ans K)) r
    → ty (Ans (litSet c ⊗Set K)) (m ++ r)
  tok⟜▷ c K m lc r x = go m lc
    where
    go : (w : ↓M tt) → w Eq.≡ (c ∷ []) → ty (Ans (litSet c ⊗Set K)) (w ++ r)
    go .(c ∷ []) Eq.refl = Ans-lit c (c ∷ r) (▷cons c r x)
