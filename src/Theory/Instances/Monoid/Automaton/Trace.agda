{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The language of a state, generated rather than matched.

   `DerivAutomaton` asks for a family `L` and a proof that `δ` computes
   its derivative.  That is the wrong way round, and it is what made a
   regex instance look like it needed Brzozowski's finiteness theorem:
   if `L` is given in advance, the states have to be languages you
   already have, closed under a *syntactic* derivative -- which does not
   terminate without quotienting by associativity, commutativity and
   idempotence.

   `Grammar/Automata/Deterministic.agda` never had that problem, because
   it defines the language:

     Trace q  ≅  ε ⊕ (⊕[ c ] literal c ⊗ Trace (δ q c))

   as a least fixed point over the transition.  The derivative square is
   then the unrolling, not an obligation, so *any* `(Q, δ, acc)` gives a
   `DerivAutomaton` with nothing left to prove.  `traceAutomaton` below
   is that packaging.

   Both directions of the square go through `Derivative/General`: the
   easy one is the transpose of `STEP` along `literal c ⊗ - ⊣ literal c ⊸ -`
   followed by the coincidence theorem, and the hard one is determinism
   -- a trace over `c ∷ m` must step by `c`, which is the precision of
   `literal`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Automaton.Trace
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool ; true≢false)
open import Cubical.Data.List using ([] ; _∷_ ; _++_)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.Unit using (tt ; tt*)
import Cubical.Data.List.Properties as L
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
import Cubical.Data.Equality as Eq
open import Cubical.Data.Equality.More using (isSet→isSetEq)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (_⊸_ ; ⊸-lam)
open import Theory.Instances.Monoid.Precise Alphabet isSetAlphabet
  using (flat ; lit⊗-nil)
open import Theory.Instances.Monoid.Derivative Alphabet isSetAlphabet using (Dl)
open import Theory.Instances.Monoid.Derivative.General Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Base Alphabet isSetAlphabet
open import Theory.Type.HLevels MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Inductive.HLevels MonEqns Alphabet (λ _ → tt)
  listPresentation

-- The state set sits at the alphabet's level.  For a concrete alphabet
-- that is `ℓ-zero`, so any small `Q` qualifies; the restriction is only
-- that `⊕e` in the code language quantifies at the variable's level.
module _ (Q : Type ℓAlph) (δ : Q → Alphabet → Q) (acc : Q → Bool) where

  data Tag : Type ℓAlph where
    stop step : Tag

  TraceTy : Q → Functor ℓM Q (λ _ → tt) tt
  TraceTy q = ⊕e Tag λ where
    stop → ⊕e (Lift ℓAlph (acc q Eq.≡ true)) λ _ → ⊗e ε· λ ()
    step → ⊕e Alphabet λ c → ⊗e _⊙_ (two (k (literal c)) (Var (δ q c)))

  Trace : Q → TheoryTy (ℓF ℓM) tt
  Trace = μ TraceTy

  ------------------------------------------------------------------
  -- Constructors and the one-step observation.

  STOP : (q : Q) → acc q Eq.≡ true → LiftTheoryTy (ℓF ℓM) εTy ⊢ Trace q
  STOP q p = roll ∘⊢ into
    where
    into : LiftTheoryTy (ℓF ℓM) εTy ⊢ ⟦ TraceTy q ⟧TheoryTy Trace
    into m x = stop , lift p , x .lower .fst , x .lower .snd .fst , λ ()

  STEP : (c : Alphabet) (q : Q) → literal c ⊗ Trace (δ q c) ⊢ Trace q
  STEP c q = roll ∘⊢ into
    where
    into : literal c ⊗ Trace (δ q c) ⊢ ⟦ TraceTy q ⟧TheoryTy Trace
    into m (ms , e , l , t , _) = step , c , ms , e , two (lift l) (lift t)

  TraceLayer : Q → TheoryTy _ tt
  TraceLayer q =
    (⊕[ c ∈ Alphabet ] (literal c ⊗ Trace (δ q c)))
      ⊕ (⊕[ _ ∈ acc q Eq.≡ true ] LiftTheoryTy (ℓF ℓM) εTy)

  unrollTrace : (q : Q) → Trace q ⊢ TraceLayer q
  unrollTrace q = fromF ∘⊢ unroll TraceTy q
    where
    fromF : ⟦ TraceTy q ⟧TheoryTy Trace ⊢ TraceLayer q
    fromF m (stop , lift p , ms , e , _) = Sum.inr (p , lift (ms , e , tt*))
    fromF m (step , c , ms , e , f) =
      Sum.inl (c , ms , e , f zero .lower , f (suc zero) .lower , tt*)

  ------------------------------------------------------------------
  -- The derivative square, generically.

  -- Easy: `STEP` transposed, then read the residual as a derivative.
  Trace→Dl : (q : Q) (c : Alphabet) → Trace (δ q c) ⊢ Dl c (Trace q)
  Trace→Dl q c =
    ∂⌈⌉→Dl (⌈gen c ⌉) {B = Trace q} ∘⊢ ⊸→∂⌈⌉ (⌈gen c ⌉) {B = Trace q} ∘⊢ ⊸-lam (STEP c q)

  -- Hard: determinism.  A trace over `c ∷ m` cannot stop, and its step
  -- must be by `c` -- both by the precision of `literal`.
  Dl→Trace : (q : Q) (c : Alphabet) → Dl c (Trace q) ⊢ Trace (δ q c)
  Dl→Trace q c m x = out (unrollTrace q (c ∷ m) x)
    where
    out : TraceLayer q (c ∷ m) → Trace (δ q c) m
    out (Sum.inr (_ , e)) = Empty.rec
      (L.¬nil≡cons (Eq.eqToPath (e .lower .snd .fst)))
    out (Sum.inl (d , ms , e , l , t , _)) =
      subst (λ x → Trace (δ q x) m) (L.cons-inj₁ headed)
        (subst (Trace (δ q d)) (L.cons-inj₂ headed) t)
      where
      -- the step's letter and the head of the word are the same letter,
      -- and its tail is the rest: `literal d` pins the splitting
      headed : d ∷ ms (suc zero) ≡ c ∷ m
      headed = flat d (ms zero) (ms (suc zero)) (c ∷ m) l e

  ------------------------------------------------------------------
  -- ...so any DFA is a derivative automaton, with nothing to prove.

  private
    tag→Bool : Tag → Bool
    tag→Bool stop = false
    tag→Bool step = true

    Bool→tag : Bool → Tag
    Bool→tag false = stop
    Bool→tag true = step

    tagRet : (t : Tag) → Bool→tag (tag→Bool t) ≡ t
    tagRet stop = refl
    tagRet step = refl

    isSetTag : isSet Tag
    isSetTag = isSetRetract tag→Bool Bool→tag tagRet isSetBool

    isSetLit : (c : Alphabet) → isSetTheoryTy (literal c)
    isSetLit c m = isProp→isSet isPropEqString

  isSetTrace : (q : Q) → isSetTheoryTy (Trace q)
  isSetTrace = isSetμ TraceTy codeIsSet
    where
    codeIsSet : (q : Q) → isSetValued (TraceTy q)
    codeIsSet q .fst = lift isSetTag
    codeIsSet q .snd stop .fst =
      lift (isOfHLevelLift 2 (isProp→isSet (isSet→isSetEq isSetBool)))
    codeIsSet q .snd stop .snd _ = λ ()
    codeIsSet q .snd step .fst = lift isSetAlphabet
    codeIsSet q .snd step .snd c zero = lift (isSetLit c)
    codeIsSet q .snd step .snd c (suc zero) = lift tt*

  -- ε is accepted only by an accepting state, and a step needs a letter
  noAcc : (q : Q) → acc q Eq.≡ false → Trace q & εTy ⊢ ⊥Ty
  noAcc q p m (t , eps) =
    out (unrollTrace q [] (Eq.transport Trace* (Eq.sym (eps .snd .fst)) t))
    where
    Trace* : String → Type _
    Trace* = Trace q

    out : TraceLayer q [] → ⊥Ty m
    out (Sum.inl (d , ms , e , l , _ , _)) =
      lit⊗-nil d (ms zero) (ms (suc zero)) l e
    out (Sum.inr (pt , _)) =
      Empty.rec (true≢false (Eq.eqToPath (Eq.sym pt Eq.∙ p)))

  traceAutomaton : isSet Q → DerivAutomaton ℓAlph (ℓF ℓM)
  traceAutomaton isSetQ = record
    { Q = Q
    ; δ = δ
    ; L = Trace
    ; δ-∂  = λ q c → Dl→Trace q c ∘⊢ ∂⌈⌉→Dl (⌈gen c ⌉)
    ; δ-∂⁻ = λ q c → Dl→∂⌈⌉ (⌈gen c ⌉) ∘⊢ Trace→Dl q c
    ; isSetQ = isSetQ
    ; isSetL = isSetTrace
    ; acc = acc
    ; accY = λ q p → STOP q p ∘⊢ liftTy
    ; accN = noAcc
    }
