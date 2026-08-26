{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- First/FollowLast disjointness for implicit automata, ported from
   `Automata/Implicit.agda`.

   These are the lemmas that *derive* the side conditions the regex
   constructions in `Implicit/RegExp` demand: a syntactic fact about the
   transition table (`fail ≡ δᵢ c`, `null ≡ false`, no transition out of an
   accepting state) becomes a semantic disjointness statement about the
   language `Parse` denotes. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Automaton.Implicit.Disjointness
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.Unit using (tt ; tt*)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.List using ([] ; _∷_)
import Cubical.Data.List.Properties as L
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet
  using (starBranch ; fold*r ; readChars)
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (_⟜_ ; ⟜-intro ; ⟜-app ; ⊗⊕ᴰ-distL ; ⊗⊕ᴰ-distR)
open import Theory.Instances.Monoid.Precise Alphabet isSetAlphabet using (flat)
open import Theory.Instances.Monoid.Automaton.Deterministic
  Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Implicit Alphabet isSetAlphabet

private variable ℓA ℓB ℓY : Level

------------------------------------------------------------------------
-- Generic facts, all about `literal`: none of them mention an automaton.

-- `A & -` commutes with a dependent sum, pointwise
&⊕ᴰ-distR : {A : TheoryTy ℓA tt} {Y : Type ℓY} {B : Y → TheoryTy ℓB tt}
  → A & (⊕[ y ∈ Y ] B y) ⊢ ⊕[ y ∈ Y ] (A & B y)
&⊕ᴰ-distR m (a , (y , b)) = y , (a , b)

⊗⊥↑-annihR : {A : TheoryTy ℓA tt} → A ⊗ ⊥Ty↑ ℓB ⊢ ⊥Ty
⊗⊥↑-annihR m (ms , e , (a , (b , _))) = b .lower

⊗⊥↑-annihL : {A : TheoryTy ℓA tt} → ⊥Ty↑ ℓB ⊗ A ⊢ ⊥Ty
⊗⊥↑-annihL m (ms , e , (b , _)) = b .lower

⊤Ty↑-intro : {A : TheoryTy ℓA tt} → A ⊢ ⊤Ty↑ ℓB
⊤Ty↑-intro m a = tt*

-- a word starting with a letter is not empty
ε∉lit⊗ : {A : TheoryTy ℓA tt} (c : Alphabet) → εTy & (＂ c ＂ ⊗ A) ⊢ ⊥Ty
ε∉lit⊗ c m ((ms , e , _) , (ns , f , (l , (a , _)))) =
  Empty.rec
    (L.¬cons≡nil
      (flat c (ns zero) (ns (suc zero)) m l f ∙ sym (Eq.eqToPath e)))

-- Two splittings of the same word whose left factors are single letters
-- agree: the letters are equal and the tails are the same word.  This is
-- `Grammar.SequentialUnambiguity`'s `same-first`, with the tails kept.
sameHead : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} (c d : Alphabet)
  → (＂ c ＂ ⊗ A) & (＂ d ＂ ⊗ B) ⊢ ⊕[ _ ∈ c ≡ d ] (＂ c ＂ ⊗ (A & B))
sameHead {A = A} {B = B} c d m
  ((ms , e , (l , (a , _))) , (ns , f , (l' , (b , _)))) =
    L.cons-inj₁ heads , (ms , e , (l , ((a , subst B tails b) , tt*)))
  where
  heads : c ∷ ms (suc zero) ≡ d ∷ ns (suc zero)
  heads = flat c (ms zero) (ms (suc zero)) m l e
        ∙ sym (flat d (ns zero) (ns (suc zero)) m l' f)

  tails : ns (suc zero) ≡ ms (suc zero)
  tails = sym (L.cons-inj₂ heads)

-- the grammar of words with a given first letter
startsWith : Alphabet → TheoryTy ℓM tt
startsWith c = ＂ c ＂ ⊗ ⊤Ty

same-first : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} (c d : Alphabet)
  → (＂ c ＂ ⊗ A) & (＂ d ＂ ⊗ B) ⊢ ⊕[ _ ∈ c ≡ d ] ⊤Ty
same-first c d = map⊕ᴰ (λ _ → ⊤Ty-intro) ∘⊢ sameHead c d

-- `¬Nullable (startsWith c)`
¬Nullable-startsWith : (c : Alphabet) → εTy & startsWith c ⊢ ⊥Ty
¬Nullable-startsWith c = ε∉lit⊗ c

------------------------------------------------------------------------

module _ {Q : Type ℓAlph} (M : ImplicitDeterministicAutomaton Q) where
  open ImplicitDeterministicAutomaton M
  open DeterministicAutomaton (IDA→DA M)
    using (Tag ; stop ; step ; TraceTy ; Trace ; STOP ; STEP
          ; TraceLayer ; unrollTrace)

  private
    Q+ : Type ℓAlph
    Q+ = FreelyAddFail+Initial Q

    isAcc : Q+ → Bool
    isAcc = isAcc' M

    δ : Q+ → Alphabet → Q+
    δ = δ' M

  Parse : TheoryTy _ tt
  Parse = Trace true initial

  ------------------------------------------------------------------
  -- One-step observation of a *code layer*, for any carrier.  This is
  -- `unrollTrace`'s `fromF` with the carrier left free, so an algebra can
  -- be written against `⊗`/`⊕` rather than against the raw tuple.

  CodeLayer : (A : Q+ → TheoryTy ℓA tt) (b : Bool) (q : Q+) → TheoryTy _ tt
  CodeLayer A b q =
    (⊕[ c ∈ Alphabet ] (＂ c ＂ ⊗ A (δ q c)))
      ⊕ (⊕[ _ ∈ b Eq.≡ isAcc q ] LiftTheoryTy (ℓF ℓM) εTy)

  fromCode : {A : Q+ → TheoryTy ℓA tt} (b : Bool) (q : Q+)
    → ⟦ TraceTy b q ⟧TheoryTy A ⊢ CodeLayer A b q
  fromCode b q m (stop p , x) = Sum.inr (p , lift (x .lower))
  fromCode b q m (step c , ms , e , f) =
    Sum.inl (c , ms , e , (f zero .lower , (f (suc zero) .lower , tt*)))

  ------------------------------------------------------------------
  -- Algebras over an accepting trace.  `fail` carries no information, so
  -- the carrier is empty there and the whole `fail` branch is refuted.

  ParseAlgCarrier : (A : FreelyAddInitial Q → TheoryTy ℓA tt)
    → Q+ → TheoryTy ℓA tt
  ParseAlgCarrier {ℓA = ℓA} A fail = ⊥Ty↑ ℓA
  ParseAlgCarrier A initial = A initial
  ParseAlgCarrier A (↑q q) = A (↑i q)

  ParseAlg : (A : FreelyAddInitial Q → TheoryTy ℓA tt) → Type _
  ParseAlg A =
    (x : Q+) → ⟦ TraceTy true x ⟧TheoryTy (ParseAlgCarrier A) ⊢ ParseAlgCarrier A x

  module _ {A : FreelyAddInitial Q → TheoryTy ℓA tt} where
    ParseAlgFail' : ⟦ TraceTy true fail ⟧TheoryTy (ParseAlgCarrier A) ⊢ ⊥Ty
    ParseAlgFail' =
      ⊕-elim (⊕ᴰ-elim λ c → ⊗⊥↑-annihR) (⊕ᴰ-elim λ ())
      ∘⊢ fromCode true fail

    ParseAlgFail : {B : TheoryTy ℓB tt}
      → ⟦ TraceTy true fail ⟧TheoryTy (ParseAlgCarrier A) ⊢ B
    ParseAlgFail = ⊥Ty-elim ∘⊢ ParseAlgFail'

  ------------------------------------------------------------------
  -- Every word has a trace at `fail`, and it rejects.  `fail` loops to
  -- itself and is never accepting, so this is a fold over the input, not
  -- a run of the automaton.

  private
    star-nil⁻ : {B : TheoryTy ℓB tt}
      → ⟦ starBranch char false ⟧TheoryTy (λ _ → B)
      ⊢ LiftTheoryTy (ℓF ℓM) εTy
    star-nil⁻ m (ms , e , _) = lift (ms , e , tt*)

    star-cons⁻ : {B : TheoryTy ℓB tt}
      → ⟦ starBranch char true ⟧TheoryTy (λ _ → B) ⊢ char ⊗ B
    star-cons⁻ m (ms , e , f) =
      ms , e , (f zero .lower , (f (suc zero) .lower , tt*))

  failTrace : ⊤Ty ⊢ Trace false fail
  failTrace = fold*r nilB consB ∘⊢ readChars
    where
    nilB : ⟦ starBranch char false ⟧TheoryTy (λ _ → Trace false fail)
         ⊢ Trace false fail
    nilB = STOP fail ∘⊢ star-nil⁻

    consB : ⟦ starBranch char true ⟧TheoryTy (λ _ → Trace false fail)
          ⊢ Trace false fail
    consB = ⊕ᴰ-elim (λ c → STEP c fail) ∘⊢ ⊗⊕ᴰ-distL ∘⊢ star-cons⁻

  ------------------------------------------------------------------
  -- Trace disjointness.  A word has at most one acceptance verdict from a
  -- given state: the `Bool` indices of two traces over the same word agree.
  --
  -- This replaces `unambiguous-⊕Trace` of the old development, which got
  -- the same fact out of `⊕[ b ] Trace b q ≅ string`.  Only the index is
  -- ever used downstream, and the index is what an induction on one trace
  -- against a one-step unrolling of the other already gives.

  module _ (b b' : Bool) where
    private
      Res : TheoryTy ℓ-zero tt
      Res = ⊕[ _ ∈ b ≡ b' ] ⊤Ty

      Carrier : Q+ → TheoryTy _ tt
      Carrier q = Trace b' q ⇒ Res

      -- two steps must step by the same letter, and then the recursive
      -- call at the common successor state supplies the verdict
      reState : (q : Q+) (c d : Alphabet) → c ≡ d
        → Trace b' (δ q d) ⊢ Trace b' (δ q c)
      reState q c d p m t = subst (λ y → Trace b' (δ q y) m) (sym p) t

      stepStep : (q : Q+) (c d : Alphabet)
        → (＂ c ＂ ⊗ Carrier (δ q c)) & (＂ d ＂ ⊗ Trace b' (δ q d)) ⊢ Res
      stepStep q c d =
        ⊕ᴰ-elim
          (λ p →
            ⊕ᴰ-elim (λ pb → σ⊕ pb ∘⊢ ⊤Ty-intro)
            ∘⊢ ⊗⊕ᴰ-distR {C = λ _ → ⊤Ty}
            ∘⊢ (id⊢ ,⊗ (⇒-app ∘⊢ (id⊢ ,&p reState q c d p))))
        ∘⊢ sameHead c d

      -- a step and a stop cannot describe the same word
      stepStop : (q : Q+) (c : Alphabet)
        → (＂ c ＂ ⊗ Carrier (δ q c))
          & (⊕[ _ ∈ b' Eq.≡ isAcc q ] LiftTheoryTy (ℓF ℓM) εTy)
        ⊢ Res
      stepStop q c =
        ⊥Ty-elim ∘⊢ ε∉lit⊗ c
        ∘⊢ ((⊕ᴰ-elim (λ _ → lowerTy) ∘⊢ π₂) ,& π₁)

      stopStep : (q : Q+)
        → εTy & (⊕[ c ∈ Alphabet ] (＂ c ＂ ⊗ Trace b' (δ q c))) ⊢ Res
      stopStep q = ⊥Ty-elim ∘⊢ ⊕ᴰ-elim (λ c → ε∉lit⊗ c) ∘⊢ &⊕ᴰ-distR

      -- both stop: the two acceptance equations meet at `isAcc q`
      stopStop : (q : Q+) → b Eq.≡ isAcc q
        → εTy & (⊕[ _ ∈ b' Eq.≡ isAcc q ] LiftTheoryTy (ℓF ℓM) εTy) ⊢ Res
      stopStop q p =
        ⊕ᴰ-elim (λ p' → σ⊕ (Eq.eqToPath p ∙ sym (Eq.eqToPath p')) ∘⊢ ⊤Ty-intro)
        ∘⊢ π₂

      disjAlg : (q : Q+) → ⟦ TraceTy b q ⟧TheoryTy Carrier ⊢ Carrier q
      disjAlg q =
        ⊕-elim
          (⊕ᴰ-elim λ c →
            ⇒-intro
              (⊕-elim&
                (⊕ᴰ-elim (λ d → stepStep q c d) ∘⊢ &⊕ᴰ-distR)
                (stepStop q c)
              ∘⊢ (id⊢ ,&p unrollTrace b' q)))
          (⊕ᴰ-elim λ p →
            ⇒-intro
              (⊕-elim& (stopStep q) (stopStop q p)
              ∘⊢ (lowerTy ,&p unrollTrace b' q)))
        ∘⊢ fromCode b q

    TraceDisj : (q : Q+) → Trace b q & Trace b' q ⊢ ⊕[ _ ∈ b ≡ b' ] ⊤Ty
    TraceDisj q = ⇒-intro⁻ (rec (TraceTy b) disjAlg q)

  -- the two verdicts are disjoint
  TraceDisj⊥ : (b b' : Bool) → (b ≡ b' → Empty.⊥) → (q : Q+)
    → Trace b q & Trace b' q ⊢ ⊥Ty
  TraceDisj⊥ b b' ne q =
    ⊕ᴰ-elim (λ p → Empty.rec (ne p)) ∘⊢ TraceDisj b b' q

  ------------------------------------------------------------------
  -- Parsing at a state.  `⊕[ b ] Trace b q` is total, and `TraceDisj⊥`
  -- says the two summands never both hold: together, the old
  -- `AcceptingTraceParser`.

  module _ (isSetQ : isSet Q) where
    open DeterministicAutomaton (IDA→DA M) using (parse)

    parseTrace : (q : Q+) → ⊤Ty ⊢ Trace true q ⊕ Trace false q
    parseTrace q =
      ⊕ᴰ-elim (λ where true → inl ; false → inr)
      ∘⊢ π q
      ∘⊢ parse (isSetFreelyAddFail+Initial Q isSetQ)
      ∘⊢ readChars

    AcceptingTraceParser : (q : Q+) → Trace true q & Trace false q ⊢ ⊥Ty
    AcceptingTraceParser = TraceDisj⊥ true false true≢false

  ------------------------------------------------------------------
  -- `c ∉ First (Parse)`.  An accepting run over a word beginning with `c`
  -- exhibits the initial transition on `c`, so a `fail` there refutes it.

  module _ (c : Alphabet) where
    private
      FirstFiber : Type ℓAlph
      FirstFiber = Σ[ q ∈ Q ] ((↑f q) ≡ δᵢ c)

      FirstRes : TheoryTy ℓAlph tt
      FirstRes = ⊕[ _ ∈ FirstFiber ] ⊤Ty

      ⟦_⟧F : FreelyAddInitial Q → TheoryTy (ℓ-max ℓM ℓAlph) tt
      ⟦ initial ⟧F = startsWith c ⇒ FirstRes
      ⟦ ↑i q ⟧F = ⊤Ty↑ (ℓ-max ℓM ℓAlph)

      firstAlg : ParseAlg ⟦_⟧F
      firstAlg fail = ParseAlgFail
      firstAlg (↑q q) = ⊤Ty↑-intro
      firstAlg initial =
        ⊕-elim
          (⊕ᴰ-elim help)
          (⊕ᴰ-elim λ _ →
            ⇒-intro
              (⊥Ty-elim ∘⊢ ¬Nullable-startsWith c ∘⊢ (lowerTy ,&p id⊢)))
        ∘⊢ fromCode true initial
        where
        help : (c' : Alphabet)
          → ＂ c' ＂ ⊗ ParseAlgCarrier ⟦_⟧F (↑f→q (δᵢ c'))
          ⊢ startsWith c ⇒ FirstRes
        help c' with δᵢ c' in eq
        ... | fail =
          ⇒-intro (⊥Ty-elim ∘⊢ ⊗⊥↑-annihR {A = ＂ c' ＂} ∘⊢ π₁)
        ... | ↑f q =
          ⇒-intro
            (⊕ᴰ-elim
               (λ c'≡c →
                 σ⊕ (q , J (λ c'' _ → (↑f q) ≡ δᵢ c'')
                           (Eq.eqToPath (Eq.sym eq)) c'≡c)
                 ∘⊢ ⊤Ty-intro)
            ∘⊢ same-first {A = ⊤Ty} {B = ⊤Ty} c' c
            ∘⊢ ((id⊢ {A = ＂ c' ＂}
                  ,⊗ ⊤Ty-intro {A = ⊤Ty↑ (ℓ-max ℓM ℓAlph)})
                ,&p id⊢ {A = startsWith c}))

    getFirstTransition : startsWith c & Parse ⊢ FirstRes
    getFirstTransition =
      ⇒-intro⁻ (rec (TraceTy true) firstAlg initial) ∘⊢ &-swap

  ¬FirstAut : (c : Alphabet) → fail ≡ δᵢ c → startsWith c & Parse ⊢ ⊥Ty
  ¬FirstAut c toFail =
    ⊕ᴰ-elim (λ x → Empty.rec (fail≢↑f (Eq.pathToEq (toFail ∙ sym (x .snd)))))
    ∘⊢ getFirstTransition c

  ------------------------------------------------------------------
  -- `¬Nullable Parse`.  `STOPᵢ` is a `Trace null initial` over the empty
  -- word; a `Parse` there would give it a second verdict.

  sound-null : Parse & εTy ⊢ ⊕[ _ ∈ true ≡ null ] ⊤Ty
  sound-null =
    TraceDisj true null initial ∘⊢ (id⊢ ,&p (STOP initial ∘⊢ liftTy))

  ¬NullableAut : null ≡ false → εTy & Parse ⊢ ⊥Ty
  ¬NullableAut isFalse =
    ⊕ᴰ-elim (λ isTrue → Empty.rec (true≢false (isTrue ∙ isFalse)))
    ∘⊢ sound-null
    ∘⊢ &-swap

  ------------------------------------------------------------------
  -- `c ∉ FollowLast Parse`.  If the automaton never leaves an accepting
  -- state on `c`, then a `Parse` extended by a word beginning with `c`
  -- runs into `fail`: it is a *rejecting* trace, and the extension is
  -- therefore not itself a `Parse`.

  module _ (c : Alphabet) (notNull : null ≡ false)
    (noTrans : (q : Q) → acc q ≡ true → fail ≡ δq q c) where
    private
      FLCarrier : FreelyAddInitial Q → TheoryTy _ tt
      FLCarrier x = Trace false (↑i→q x) ⟜ startsWith c

      flAlg : ParseAlg FLCarrier
      flAlg fail = ParseAlgFail
      flAlg initial =
        ⊕-elim
          (⊕ᴰ-elim λ c' →
            ⟜-intro (STEP c' initial ∘⊢ (id⊢ ,⊗ stepConv c') ∘⊢ ⊗-assoc))
          (⊕ᴰ-elim λ p → Empty.rec (true≢false (Eq.eqToPath p ∙ notNull)))
        ∘⊢ fromCode true initial
        where
        stepConv : (c' : Alphabet)
          → ParseAlgCarrier FLCarrier (↑f→q (δᵢ c')) ⊗ startsWith c
          ⊢ Trace false (↑f→q (δᵢ c'))
        stepConv c' with δᵢ c'
        ... | fail = ⊥Ty-elim ∘⊢ ⊗⊥↑-annihL {A = startsWith c}
        ... | ↑f q'' = ⟜-app
      flAlg (↑q q) =
        ⊕-elim
          (⊕ᴰ-elim λ c' →
            ⟜-intro (STEP c' (↑q q) ∘⊢ (id⊢ ,⊗ stepConv c') ∘⊢ ⊗-assoc))
          (⊕ᴰ-elim λ accEq →
            ⟜-intro (closeAtAcc accEq ∘⊢ ⊗-unit-l ∘⊢ (lowerTy ,⊗ id⊢)))
        ∘⊢ fromCode true (↑q q)
        where
        -- at an accepting state there is no `c`-transition, so the
        -- continuation is the rejecting run at `fail`
        closeAtAcc : true Eq.≡ acc q → startsWith c ⊢ Trace false (↑q q)
        closeAtAcc accEq =
          STEP c (↑q q)
          ∘⊢ (id⊢ ,⊗ subst (λ d → ⊤Ty ⊢ Trace false (↑f→q d))
                        (noTrans q (sym (Eq.eqToPath accEq)))
                        failTrace)

        stepConv : (c' : Alphabet)
          → ParseAlgCarrier FLCarrier (↑f→q (δq q c')) ⊗ startsWith c
          ⊢ Trace false (↑f→q (δq q c'))
        stepConv c' with δq q c'
        ... | fail = ⊥Ty-elim ∘⊢ ⊗⊥↑-annihL {A = startsWith c}
        ... | ↑f q'' = ⟜-app

    extendC : Parse ⊗ startsWith c ⊢ Trace false initial
    extendC = ⟜-app ∘⊢ (rec (TraceTy true) flAlg initial ,⊗ id⊢)

    ¬FollowLastAut : (Parse ⊗ startsWith c) & Parse ⊢ ⊥Ty
    ¬FollowLastAut =
      TraceDisj⊥ false true (λ p → true≢false (sym p)) initial
      ∘⊢ ((extendC ∘⊢ π₁) ,& π₂)
