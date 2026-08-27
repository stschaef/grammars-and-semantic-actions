{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Deterministic automata: a state set, an initial state, an acceptance
   predicate, a transition.  Everything else is generated.

     Trace b q  ≅  (b ≡ isAcc q → ε)  ⊕  (⊕[ c ] literal c ⊗ Trace b (δ q c))

   `Tag` carries its own payload, so each functor branch is a bare `k` or
   `k ⊗e Var` and the constructors are `roll ∘ σ⊕ tag`.  Indexing by a
   `Bool` makes `⊕[ b ] Trace b q` total: rejection is a `Trace false`
   rather than the absence of a trace, so `parse` is a function. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Automaton.Deterministic
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool ; true≢false)
open import Cubical.Data.Unit using (tt ; tt*)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.List using ([] ; _∷_)
import Cubical.Data.List.Properties as L
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open import Cubical.Data.Sum as Sum using (_⊎_ ; isSet⊎)
open import Cubical.Data.Equality.More using (isSet→isSetEq)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar.Guarded Alphabet isSetAlphabet
  using (char-¬Nullable ; fold*g)
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⊗⊕ᴰ-distL ; ⊗⊕ᴰ-distR ; _⊸_ ; ⊸-lam)
open import Theory.Instances.Monoid.Convolution Alphabet isSetAlphabet
  using (⟦⊗e⟧ ; ⟦⊗e⟧⁻ ; ⟦⊗e⟧-η ; ⟦⊗e⟧⁻-nat)
open import Theory.Instances.Monoid.Precise Alphabet isSetAlphabet using (Dl-ε ; Dl-lit⊗)
open import Theory.Instances.Monoid.Derivative Alphabet isSetAlphabet using (Dl ; Dl-map)
open import Theory.Instances.Monoid.Derivative.General Alphabet isSetAlphabet
open import Theory.Type.HLevels MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Inductive.HLevels MonEqns Alphabet (λ _ → tt)
  listPresentation


private variable ℓQ ℓB : Level

-- The state set is level-polymorphic.  `Functor ℓA X` carries `X` at its
-- own level, so only the *index* has to accommodate the alphabet -- the
-- summand index `Tag` mentions `Alphabet`, and `⊕e` demands it sit at
-- `X`'s level.  Hence `QL = Lift ℓAlph Q`; the carrier stays at `ℓM`, so
-- no grammar in the code is lifted.
record DeterministicAutomaton (Q : Type ℓQ)
  : Type (ℓ-suc (ℓ-max ℓQ ℓAlph)) where
  field
    init  : Q
    isAcc : Q → Bool
    δ     : Q → Alphabet → Q

  QL : Type (ℓ-max ℓQ ℓAlph)
  QL = Lift ℓAlph Q

  -- the level a trace lands at: `μ` adds the index's level to the code's
  ℓT : Level
  ℓT = ℓ-max (ℓF ℓM) (ℓ-max ℓQ ℓAlph)

  data Tag (b : Bool) (q : Q) : Type (ℓ-max ℓQ ℓAlph) where
    stop : b Eq.≡ isAcc q → Tag b q
    step : Alphabet → Tag b q

  -- the labelled summand, named so its two directions can be stated
  stepBranch : (q : Q) (c : Alphabet) → Functor ℓM QL (λ _ → tt) tt
  stepBranch q c = ⊗e _⊙_ (two (k (literal c)) (Var (lift (δ q c))))

  TraceTy : Bool → QL → Functor ℓM QL (λ _ → tt) tt
  TraceTy b (lift q) = ⊕e (Tag b q) λ where
    (stop _) → k εTy
    (step c) → stepBranch q c

  Trace : Bool → Q → TheoryTy _ tt
  Trace b q = μ (TraceTy b) (lift q)

  -- an algebra over the trace code, indexed as `rec` wants it
  TraceAlg : Bool → (QL → TheoryTy ℓB tt) → Type _
  TraceAlg b A = ∀ q → ⟦ TraceTy b q ⟧TheoryTy A ⊢ A q

  -- The `step` summand, unbundled: a DSL composite rather than a tuple, so
  -- that a labelled-transition branch never binds a model element.
  module _ {ℓB} {A : QL → TheoryTy ℓB tt} where
    step-out : ∀ {q} (c : Alphabet)
      → ⟦ stepBranch q c ⟧TheoryTy A ⊢ literal c ⊗ A (lift (δ q c))
    step-out c = ⊗-map lowerTy lowerTy ∘⊢ ⟦⊗e⟧ _ _

    step-in : ∀ {q} (c : Alphabet)
      → literal c ⊗ A (lift (δ q c)) ⊢ ⟦ stepBranch q c ⟧TheoryTy A
    step-in c = ⟦⊗e⟧⁻ _ _ ∘⊢ ⊗-map liftTy liftTy

    step-η : ∀ {q} (c : Alphabet) → step-in {q = q} c ∘⊢ step-out c ≡ id⊢
    step-η c = ⟦⊗e⟧-η _ _

  map-step : ∀ {ℓB ℓC} {A : QL → TheoryTy ℓB tt} {B : QL → TheoryTy ℓC tt}
    (f : ∀ q → A q ⊢ B q) (q : Q) (c : Alphabet)
    → map (stepBranch q c) f
      ≡ step-in {A = B} c ∘⊢ ⊗-map id⊢ (f (lift (δ q c))) ∘⊢ step-out {A = A} c
  map-step {A = A} f q c =
    sym (cong (λ z → map (stepBranch q c) f ∘⊢ z) (⟦⊗e⟧-η _ _ {A = A}))
    ∙ cong (λ z → z ∘⊢ ⟦⊗e⟧ {A = A} _ _) (⟦⊗e⟧⁻-nat _ _ f)

  -- Constructors: pick the tag, roll.

  -- `stop` at a given bit, with the acceptance equation supplied.  The
  -- unprimed form is the common case, `b := isAcc q`.
  STOP' : {b : Bool} {q : Q} → b Eq.≡ isAcc q → εTy ⊢ Trace b q
  STOP' {b = b} {q = q} p = roll ∘⊢ σ⊕ {Y = Tag b q} (stop p) ∘⊢ liftTy

  STOP : (q : Q) → LiftTheoryTy ℓT εTy ⊢ Trace (isAcc q) q
  STOP q = roll ∘⊢ σ⊕ {Y = Tag (isAcc q) q} (stop Eq.refl)

  STEP : {b : Bool} (c : Alphabet) (q : Q)
    → literal c ⊗ Trace b (δ q c) ⊢ Trace b q
  STEP {b = b} c q = roll ∘⊢ σ⊕ {Y = Tag b q} (step c) ∘⊢ STEP-branch
    where
    -- the only plumbing: a tensor's factors enter the code lifted, as in
    -- `KleeneStar.CONS-branch`
    STEP-branch : {b : Bool} → literal c ⊗ Trace b (δ q c)
      ⊢ ⟦ ⊗e _⊙_ (two (k (literal c)) (Var (lift (δ q c)))) ⟧TheoryTy
          (λ x → Trace b (x .lower))
    STEP-branch m (ms , e , l , t , _) = ms , e , two (lift l) (lift t)

  -- The transition *is* the derivative.
  --
  -- Not an assumption -- there is no field asking for this, because the
  -- trace is generated by `δ` rather than checked against a language
  -- given in advance.  Both directions are stated against `∂` of
  -- `Derivative/General` and land on `Dl` through its coincidence
  -- theorem at a representable.

  TraceLayer : Bool → Q → TheoryTy _ tt
  TraceLayer b q =
    (⊕[ c ∈ Alphabet ] (literal c ⊗ Trace b (δ q c)))
      ⊕ (⊕[ _ ∈ b Eq.≡ isAcc q ] LiftTheoryTy ℓT εTy)

  unrollTrace : (b : Bool) (q : Q) → Trace b q ⊢ TraceLayer b q
  unrollTrace b q = fromF ∘⊢ unroll (TraceTy b) (lift q)
    where
    fromF : ⟦ TraceTy b (lift q) ⟧TheoryTy (λ x → Trace b (x .lower))
          ⊢ TraceLayer b q
    fromF m (stop p , x) = Sum.inr (p , x)
    fromF m (step c , ms , e , f) =
      Sum.inl (c , ms , e , f zero .lower , f (suc zero) .lower , tt*)

  -- The same one-step observation with the carrier left free, so that an
  -- algebra can be written against `⊗`/`⊕` rather than the raw tuple.
  CodeLayer : (A : QL → TheoryTy ℓB tt) (b : Bool) (q : Q) → TheoryTy _ tt
  CodeLayer A b q =
    (⊕[ c ∈ Alphabet ] (literal c ⊗ A (lift (δ q c))))
      ⊕ (⊕[ _ ∈ b Eq.≡ isAcc q ] LiftTheoryTy ℓT εTy)

  fromCode : {A : QL → TheoryTy ℓB tt} (b : Bool) (q : Q)
    → ⟦ TraceTy b (lift q) ⟧TheoryTy A ⊢ CodeLayer A b q
  fromCode b q m (stop p , x) = Sum.inr (p , lift (x .lower))
  fromCode b q m (step c , ms , e , f) =
    Sum.inl (c , ms , e , (f zero .lower , (f (suc zero) .lower , tt*)))

  -- `STEP` transposed along `literal c ⊗ - ⊣ literal c ⊸ -`
  Trace→∂ : (b : Bool) (q : Q) (c : Alphabet)
    → Trace b (δ q c) ⊢ ∂[ literal c ] (Trace b q)
  Trace→∂ b q c = ⊸→∂⌈⌉ (⌈gen c ⌉) {B = Trace b q} ∘⊢ ⊸-lam (STEP c q)

  Trace→Dl : (b : Bool) (q : Q) (c : Alphabet)
    → Trace b (δ q c) ⊢ Dl c (Trace b q)
  Trace→Dl b q c = ∂⌈⌉→Dl (⌈gen c ⌉) {B = Trace b q} ∘⊢ Trace→∂ b q c

  -- ...and back, by determinism: a trace over `c ∷ m` cannot stop, and
  -- its step must be by `c`.  Both are the precision of `literal`.
  -- `Dl c` is reindexing, so it commutes with `⊕` and `⊕ᴰ` on the nose
  -- and the whole proof is the two precision facts of `Precise`:
  -- `Dl-ε` kills the stop branch, `Dl-lit⊗` pins the step's letter.
  Dl→Trace : (b : Bool) (q : Q) (c : Alphabet)
    → Dl c (Trace b q) ⊢ Trace b (δ q c)
  Dl→Trace b q c =
    ⊕-elim
      (⊕ᴰ-elim λ d → ⊕ᴰ-elim (onState d) ∘⊢ Dl-lit⊗ c d)
      (⊕ᴰ-elim λ _ → ⊥Ty-elim ∘⊢ Dl-ε c ∘⊢ Dl-map c (lowerTy {ℓB = ℓT} {A = εTy}))
    ∘⊢ Dl-map c (unrollTrace b q)
    where
    onState : (d : Alphabet) → d ≡ c → Trace b (δ q d) ⊢ Trace b (δ q c)
    onState d p m = subst (λ y → Trace b (δ q y) m) p

  ∂→Trace : (b : Bool) (q : Q) (c : Alphabet)
    → ∂[ literal c ] (Trace b q) ⊢ Trace b (δ q c)
  ∂→Trace b q c = Dl→Trace b q c ∘⊢ ∂⌈⌉→Dl (⌈gen c ⌉) {B = Trace b q}

  -- `parse`: the whole table, in one pass.

  private
    -- `Tag b q` is `(b ≡ isAcc q) ⊎ Alphabet`, by its two constructors
    isSetTag : (b : Bool) (q : Q) → isSet (Tag b q)
    isSetTag b q = isSetRetract to from ret
      (isSet⊎ (isProp→isSet (isSet→isSetEq isSetBool)) isSetAlphabet)
      where
      to : Tag b q → (b Eq.≡ isAcc q) ⊎ Alphabet
      to (stop p) = Sum.inl p
      to (step c) = Sum.inr c

      from : (b Eq.≡ isAcc q) ⊎ Alphabet → Tag b q
      from (Sum.inl p) = stop p
      from (Sum.inr c) = step c

      ret : (t : Tag b q) → from (to t) ≡ t
      ret (stop p) = refl
      ret (step c) = refl

    codeIsSet : (b : Bool) (q : QL) → isSetValued (TraceTy b q)
    codeIsSet b (lift q) .fst = lift (isSetTag b q)
    codeIsSet b (lift q) .snd (stop _) = lift (isSet⊗ ε· _ _ λ ())
    codeIsSet b (lift q) .snd (step c) zero =
      lift λ m → isProp→isSet isPropEqString
    codeIsSet b (lift q) .snd (step c) (suc zero) = lift tt*

  isSetTrace : (b : Bool) (q : Q) → isSetTheoryTy (Trace b q)
  isSetTrace b q = isSetμ (TraceTy b) (codeIsSet b) (lift q)

  module _ (isSetQ : isSet Q) where
    private
      Table : TheoryTy _ tt
      Table = &[ q ∈ Q ] (⊕[ b ∈ Bool ] Trace b q)

      isSetTable : isSetTheoryTy Table
      isSetTable = isSet&ᴰ λ q → isSet⊕ᴰ isSetBool λ b → isSetTrace b q

      nil : εTy ⊢ Table
      nil = &ᴰ-intro λ q → σ⊕ (isAcc q) ∘⊢ STOP q ∘⊢ liftTy

      cons : char ⊗ Table ⊢ Table
      cons = &ᴰ-intro λ q →
        ⊕ᴰ-elim (λ c →
          ⊕ᴰ-elim (λ b → σ⊕ b ∘⊢ STEP c q)
          ∘⊢ ⊗⊕ᴰ-distR {C = λ b → Trace b (δ q c)}
          ∘⊢ (id⊢ ,⊗ π {A = λ q → ⊕[ b ∈ Bool ] Trace b q} (δ q c)))
        ∘⊢ ⊗⊕ᴰ-distL

    parse : char * ⊢ &[ q ∈ Q ] (⊕[ b ∈ Bool ] Trace b q)
    parse = fold*g (Table , isSetTable) char-¬Nullable nil cons

    parseInit : char * ⊢ ⊕[ b ∈ Bool ] Trace b init
    parseInit = π init ∘⊢ parse

-- Dead states.
--
-- A state is dead when nothing is accepted from it.  Two Boolean facts
-- say so -- `δ` never leaves the dead set, and a dead state rejects --
-- and `dead-empty` is then a structural recursion on the trace: `stop`
-- contradicts `dead-rej`, `step` recurses by `dead-δ`.  A consumer that
-- can test deadness therefore refutes a run without inspecting one.
module _ {Q : Type ℓQ} (M : DeterministicAutomaton Q) where
  open DeterministicAutomaton M

  record Deadness : Type (ℓ-max ℓQ ℓAlph) where
    field
      isDead   : Q → Bool
      dead-δ   : (q : Q) (c : Alphabet) → isDead q Eq.≡ true
               → isDead (δ q c) Eq.≡ true
      dead-rej : (q : Q) → isDead q Eq.≡ true → isAcc q Eq.≡ false

  -- the always-available one: nothing is known dead, and nothing is
  -- gained.  Existing users pass this and behave exactly as before.
  noDead : Deadness
  noDead .Deadness.isDead _ = false
  noDead .Deadness.dead-δ _ _ ()
  noDead .Deadness.dead-rej _ ()

  module _ (D : Deadness) where
    open Deadness D

    dead-empty : (q : Q) → isDead q Eq.≡ true
      → (w : String) → Trace true q w → Empty.⊥
    dead-empty q d w (roll .w (stop p , x)) =
      true≢false (Eq.eqToPath (p Eq.∙ dead-rej q d))
    dead-empty q d w (roll .w (step c , ms , e , f)) =
      dead-empty (δ q c) (dead-δ q c d)
        (ms (suc zero)) (f (suc zero) .lower)
