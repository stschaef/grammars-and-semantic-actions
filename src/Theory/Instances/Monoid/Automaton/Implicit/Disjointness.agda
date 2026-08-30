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
open import Theory.Instances.Monoid.Precise Alphabet isSetAlphabet
  using (flat ; ε∉lit⊗ ; sameHead)
open import Theory.Instances.Monoid.SequentialUnambiguity.First
  Alphabet isSetAlphabet using (startsWith)
import Theory.Instances.Monoid.Automaton.Disjoint Alphabet isSetAlphabet as D
open import Theory.Instances.Monoid.Automaton.Deterministic
  Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Implicit Alphabet isSetAlphabet

private variable ℓA ℓB ℓY : Level

-- Generic facts, all about `literal`: none of them mention an automaton.

&⊕ᴰ-distR : {A : TheoryTy ℓA tt} {Y : Type ℓY} {B : Y → TheoryTy ℓB tt}
  → A & (⊕[ y ∈ Y ] B y) ⊢ ⊕[ y ∈ Y ] (A & B y)
&⊕ᴰ-distR m (a , (y , b)) = y , (a , b)

⊗⊥↑-annihR : {A : TheoryTy ℓA tt} → A ⊗ ⊥Ty↑ ℓB ⊢ ⊥Ty
⊗⊥↑-annihR m (ms , e , (a , (b , _))) = b .lower

⊗⊥↑-annihL : {A : TheoryTy ℓA tt} → ⊥Ty↑ ℓB ⊗ A ⊢ ⊥Ty
⊗⊥↑-annihL m (ms , e , (b , _)) = b .lower

⊤Ty↑-intro : {A : TheoryTy ℓA tt} → A ⊢ ⊤Ty↑ ℓB
⊤Ty↑-intro m a = tt*

same-first : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} (c d : Alphabet)
  → (＂ c ＂ ⊗ A) & (＂ d ＂ ⊗ B) ⊢ ⊕[ _ ∈ c ≡ d ] ⊤Ty
same-first c d = map⊕ᴰ (λ _ → ⊤Ty-intro) ∘⊢ sameHead c d


module _ {Q : Type ℓAlph} (M : ImplicitDeterministicAutomaton Q) where
  open ImplicitDeterministicAutomaton M
  open DeterministicAutomaton (IDA→DA M)
    using (Tag ; stop ; step ; TraceTy ; Trace ; STOP ; STEP
          ; TraceLayer ; unrollTrace ; QL ; ℓT)
  private module DA = DeterministicAutomaton (IDA→DA M)

  private
    Q+ : Type ℓAlph
    Q+ = FreelyAddFail+Initial Q

    isAcc : Q+ → Bool
    isAcc = isAcc' M

    δ : Q+ → Alphabet → Q+
    δ = δ' M

  Parse : TheoryTy _ tt
  Parse = Trace true initial

  -- Algebras over an accepting trace.  `fail` carries no information, so
  -- the carrier is empty there and the whole `fail` branch is refuted.
  -- `CodeLayer`/`fromCode` -- the one-step observation with the carrier
  -- left free -- now come from `Automaton.Deterministic`.

  CodeLayer : (A : QL → TheoryTy ℓA tt) (b : Bool) (q : Q+) → TheoryTy _ tt
  CodeLayer = DA.CodeLayer

  fromCode : {A : QL → TheoryTy ℓA tt} (b : Bool) (q : Q+)
    → ⟦ TraceTy b (lift q) ⟧TheoryTy A ⊢ CodeLayer A b q
  fromCode = DA.fromCode

  ParseAlgCarrier : (A : FreelyAddInitial Q → TheoryTy ℓA tt)
    → Q+ → TheoryTy ℓA tt
  ParseAlgCarrier {ℓA = ℓA} A fail = ⊥Ty↑ ℓA
  ParseAlgCarrier A initial = A initial
  ParseAlgCarrier A (↑q q) = A (↑i q)

  ParseAlgCarrier↑ : (A : FreelyAddInitial Q → TheoryTy ℓA tt)
    → QL → TheoryTy ℓA tt
  ParseAlgCarrier↑ A x = ParseAlgCarrier A (x .lower)

  ParseAlg : (A : FreelyAddInitial Q → TheoryTy ℓA tt) → Type _
  ParseAlg A =
    (x : Q+) → ⟦ TraceTy true (lift x) ⟧TheoryTy (ParseAlgCarrier↑ A)
             ⊢ ParseAlgCarrier A x

  -- `rec` indexes by `QL`; algebras are written over `Q+`.  `Lift` has η,
  -- so the adapter is invisible in every branch.
  ParseAlg↑ : {A : FreelyAddInitial Q → TheoryTy ℓA tt} → ParseAlg A
    → (x : QL) → ⟦ TraceTy true x ⟧TheoryTy (ParseAlgCarrier↑ A)
               ⊢ ParseAlgCarrier↑ A x
  ParseAlg↑ alg (lift x) = alg x

  recParse : {A : FreelyAddInitial Q → TheoryTy ℓA tt} → ParseAlg A
    → (q : Q+) → Trace true q ⊢ ParseAlgCarrier A q
  recParse alg q = rec (TraceTy true) (ParseAlg↑ alg) (lift q)

  module _ {A : FreelyAddInitial Q → TheoryTy ℓA tt} where
    ParseAlgFail' :
      ⟦ TraceTy true (lift fail) ⟧TheoryTy (ParseAlgCarrier↑ A) ⊢ ⊥Ty
    ParseAlgFail' =
      ⊕-elim (⊕ᴰ-elim λ c → ⊗⊥↑-annihR) (⊕ᴰ-elim λ ())
      ∘⊢ fromCode true fail

    ParseAlgFail : {B : TheoryTy ℓB tt}
      → ⟦ TraceTy true (lift fail) ⟧TheoryTy (ParseAlgCarrier↑ A) ⊢ B
    ParseAlgFail = ⊥Ty-elim ∘⊢ ParseAlgFail'

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

  TraceDisj : (b b' : Bool) (q : Q+)
    → Trace b q & Trace b' q ⊢ ⊕[ _ ∈ b ≡ b' ] ⊤Ty
  TraceDisj b b' = D.TraceDisj (IDA→DA M) b b'

  TraceDisj⊥ : (b b' : Bool) → (b ≡ b' → Empty.⊥) → (q : Q+)
    → Trace b q & Trace b' q ⊢ ⊥Ty
  TraceDisj⊥ b b' ne q =
    ⊕ᴰ-elim (λ p → Empty.rec (ne p)) ∘⊢ TraceDisj b b' q

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
              (⊥Ty-elim ∘⊢ ε∉lit⊗ {A = ⊤Ty} c ∘⊢ (lowerTy ,&p id⊢)))
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
      ⇒-intro⁻ (recParse firstAlg initial) ∘⊢ &-swap

  ¬FirstAut : (c : Alphabet) → fail ≡ δᵢ c → startsWith c & Parse ⊢ ⊥Ty
  ¬FirstAut c toFail =
    ⊕ᴰ-elim (λ x → Empty.rec (fail≢↑f (Eq.pathToEq (toFail ∙ sym (x .snd)))))
    ∘⊢ getFirstTransition c

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
    extendC = ⟜-app ∘⊢ (recParse flAlg initial ,⊗ id⊢)

    ¬FollowLastAut : (Parse ⊗ startsWith c) & Parse ⊢ ⊥Ty
    ¬FollowLastAut =
      TraceDisj⊥ false true (λ p → true≢false (sym p)) initial
      ∘⊢ ((extendC ∘⊢ π₁) ,& π₂)
