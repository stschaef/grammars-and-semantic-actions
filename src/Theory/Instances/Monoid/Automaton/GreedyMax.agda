{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Maximal munch, with maximality in the type.

   `Automaton/Greedy`'s `GreedyAt (L q) (L q')` leaves `q'` an
   unconstrained existential, so its refutation is satisfied by any state
   with an empty language.  `TraceTo q q'` gives the trace both endpoints,
   which forces the end state, and extending stays O(1) -- it is `STEP`.
   `GreedyMax→Greedy` maps the cheap state-indexed witness into
   `Greedy/Base`'s self-certifying word-indexed one; the content is
   `cancel`, that a `TraceTo q q'` over `u` splits any run over `u ++ z`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Automaton.GreedyMax
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool ; true≢false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
import Cubical.Data.List.Properties as L
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Unit using (tt ; tt*)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_ ; isSet⊎)
open import Cubical.Data.Equality.More using (isSet→isSetEq)
import Cubical.Data.Equality as Eq
import Cubical.Data.Empty as Empty

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar.Guarded Alphabet isSetAlphabet
  using (¬Nullable ; ⊗-¬Nullable ; ⊕-¬Nullable ; char-¬Nullable
       ; literal-¬Nullable ; fold*g)
open import Theory.Instances.Monoid.Greedy.Base Alphabet isSetAlphabet
  using (Greedy ; char⁺ ; noExt-step)
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⊗⊕ᴰ-distL ; ⊗⊕ᴰ-distR ; &⊕ᴰ-distL ; _⊸_)
open import Theory.Instances.Monoid.Derivative.General Alphabet isSetAlphabet
  using (⊸→∂⌈⌉)
open import Theory.Instances.Monoid.Precise Alphabet isSetAlphabet
  using (flat ; flatEq ; lit⊗-nil)
open import Theory.Instances.Monoid.Automaton.Deterministic
  Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Convolution Alphabet isSetAlphabet
  using (⟦⊗e⟧ ; ⟦⊗e⟧⁻)
open import Theory.Instances.Monoid.Automaton.Unambiguous
  Alphabet isSetAlphabet using (isPropεTy ; unambiguous-Trace)
open import Theory.Instances.Monoid.Automaton.Greedy Alphabet isSetAlphabet
  using (¬Nullable-map ; &-¬NullableR ; ⊕ᴰ-¬Nullable ; char⁺-¬Nullable
       ; ¬Nullable→¬ε ; ¬Nullable→char⁺)
open import Theory.Type.Decidable.Base MonEqns Alphabet (λ _ → tt)
  listPresentation
open import Theory.Type.HLevels MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Inductive.HLevels MonEqns Alphabet (λ _ → tt)
  listPresentation

private variable ℓA ℓB ℓL : Level

module _ {Q : Type ℓAlph} (M : DeterministicAutomaton Q) where
  open DeterministicAutomaton M

  private
    L : Q → TheoryTy _ tt
    L q = Trace true q

  -- Traces with both endpoints named.

  -- the `Tag` of `Deterministic`, with the acceptance equation replaced
  -- by an equation on the *end state*: stopping is allowed only there.
  data TagTo (q' q : Q) : Type ℓAlph where
    stop : q Eq.≡ q' → TagTo q' q
    step : Alphabet → TagTo q' q

  TraceToTy : (q' : Q) (q : Q) → Functor ℓM Q (λ _ → tt) tt
  TraceToTy q' q = ⊕e (TagTo q' q) λ where
    (stop _) → k εTy
    (step c) → ⊗e _⊙_ (two (k (literal c)) (Var (δ q c)))

  -- `TraceTo q q'`: a run from `q` that *ends* at `q'`.  The end state is
  -- the recursion's parameter, the start state its index.
  TraceTo : Q → Q → TheoryTy _ tt
  TraceTo q q' = μ (TraceToTy q') q

  STOPTo : (q : Q) → LiftTheoryTy (ℓF ℓM) εTy ⊢ TraceTo q q
  STOPTo q = roll ∘⊢ σ⊕ {Y = TagTo q q} (stop Eq.refl)

  STEPTo : (c : Alphabet) (q q' : Q)
    → literal c ⊗ TraceTo (δ q c) q' ⊢ TraceTo q q'
  STEPTo c q q' = roll ∘⊢ σ⊕ {Y = TagTo q' q} (step c) ∘⊢ branch
    where
    branch : literal c ⊗ TraceTo (δ q c) q'
      ⊢ ⟦ ⊗e _⊙_ (two (k (literal c)) (Var (δ q c))) ⟧TheoryTy
          (μ (TraceToTy q'))
    branch = ⟦⊗e⟧⁻ _ _ ∘⊢ ⊗-map liftTy liftTy

  TraceToLayer : Q → Q → TheoryTy _ tt
  TraceToLayer q q' =
    (⊕[ c ∈ Alphabet ] (literal c ⊗ TraceTo (δ q c) q'))
      ⊕ (⊕[ _ ∈ q Eq.≡ q' ] LiftTheoryTy (ℓF ℓM) εTy)

  unrollTraceTo : (q q' : Q) → TraceTo q q' ⊢ TraceToLayer q q'
  unrollTraceTo q q' = fromF ∘⊢ unroll (TraceToTy q') q
    where
    fromF : ⟦ TraceToTy q' q ⟧TheoryTy (μ (TraceToTy q'))
      ⊢ TraceToLayer q q'
    fromF = ⊕ᴰ-elim λ where
      (stop p) → inr ∘⊢ σ⊕ p
      (step c) → inl ∘⊢ σ⊕ c ∘⊢ ⊗-map lowerTy lowerTy ∘⊢ ⟦⊗e⟧ _ _

  -- The bridge to `Trace`.

  TraceTo→Trace : (b : Bool) (q q' : Q) → b Eq.≡ isAcc q'
    → TraceTo q q' ⊢ Trace b q
  TraceTo→Trace b q q' pf = rec (TraceToTy q') alg q
    where
    stopCase : (r : Q) → r Eq.≡ q' → LiftTheoryTy (ℓF ℓM) εTy ⊢ Trace b r
    stopCase r p =
      Eq.transport (λ bb → LiftTheoryTy (ℓF ℓM) εTy ⊢ Trace bb r)
        (Eq.sym (pf Eq.∙ Eq.sym (Eq.ap isAcc p))) (STOP r)

    alg : (r : Q) → ⟦ TraceToTy q' r ⟧TheoryTy (Trace b) ⊢ Trace b r
    alg r = ⊕ᴰ-elim λ where
      (stop p) → stopCase r p
      (step c) → STEP c r ∘⊢ ⊗-map lowerTy lowerTy ∘⊢ ⟦⊗e⟧ _ _

  -- `Trace b q` is `⊕[ q' ] (b ≡ isAcc q') × TraceTo q q'`
  Trace→TraceTo : (b : Bool) (q : Q)
    → Trace b q ⊢ ⊕[ q' ∈ Q ] (⊕[ _ ∈ b Eq.≡ isAcc q' ] TraceTo q q')
  Trace→TraceTo b q = rec (TraceTy b) alg (lift q)
    where
    Ans : Q → TheoryTy _ tt
    Ans r = ⊕[ q' ∈ Q ] (⊕[ _ ∈ b Eq.≡ isAcc q' ] TraceTo r q')

    alg : (r : QL) → ⟦ TraceTy b r ⟧TheoryTy (λ x → Ans (x .lower))
        ⊢ Ans (r .lower)
    alg (lift r) m (stop p , x) = r , p , STOPTo r m x
    alg (lift r) m (step c , ms , e , f) =
      f (suc zero) .lower .fst
      , f (suc zero) .lower .snd .fst
      , STEPTo c r (f (suc zero) .lower .fst) m
          (ms , e , f zero .lower , f (suc zero) .lower .snd .snd , tt*)

  -- the two together.  `bridge` is the forward map of `Trace≅TraceTo`
  -- below; its section is free from the unambiguity of `Trace`.
  BridgeTy : Bool → Q → TheoryTy _ tt
  BridgeTy b q = ⊕[ q' ∈ Q ] (⊕[ _ ∈ b Eq.≡ isAcc q' ] TraceTo q q')

  bridge : (b : Bool) (q : Q) → BridgeTy b q ⊢ Trace b q
  bridge b q = ⊕ᴰ-elim λ q' → ⊕ᴰ-elim λ p → TraceTo→Trace b q q' p

  bridge-section : (b : Bool) (q : Q)
    → bridge b q ∘⊢ Trace→TraceTo b q ≡ id⊢
  bridge-section b q =
    funExt λ m → funExt λ t → unambiguous-Trace M b q m _ t

  -- The end state is a function of the word: `δ*`.

  δ* : Q → String → Q
  δ* q [] = q
  δ* q (c ∷ w) = δ* (δ q c) w

  private
    endStop : (q q' : Q) (w : String) → q Eq.≡ q' → [] Eq.≡ w
      → δ* q w Eq.≡ q'
    endStop q .q .[] Eq.refl Eq.refl = Eq.refl

    endStep : (q q' : Q) (c : Alphabet) (w₁ w : String) → (c ∷ w₁) Eq.≡ w
      → δ* (δ q c) w₁ Eq.≡ q' → δ* q w Eq.≡ q'
    endStep q q' c w₁ .(c ∷ w₁) Eq.refl h = h

  endState : (q q' : Q) (w : String) → TraceTo q q' w → δ* q w Eq.≡ q'
  endState q q' w (roll .w (stop p , x)) =
    endStop q q' w p (x .lower .snd .fst)
  endState q q' w (roll .w (step c , ms , e , f)) =
    endStep q q' c (ms (suc zero)) w
      (flatEq c (ms zero) (ms (suc zero)) w (f zero .lower) e)
      (endState (δ q c) q' (ms (suc zero)) (f (suc zero) .lower))

  -- Cancellation: `δ` really is followed.
  --
  -- If `u` takes `q` to `q'` and `u ++ z` is a run of `q`, then `z` is a
  -- run of `q'`.  Induction on the `TraceTo`; the `Trace` is inverted at
  -- each step by the precision of `literal` (`flatEq` + cons-injectivity),
  -- exactly as in `Automaton/Unambiguous`.

  private
    cancel-stop : (b : Bool) (q q' : Q) (u z : String)
      → q Eq.≡ q' → [] Eq.≡ u
      → Trace b q (u ++ z) → Trace b q' z
    cancel-stop b q .q .[] z Eq.refl Eq.refl t = t

    -- the recursive call arrives as `k`: a `where` binding would hide the
    -- structural descent, so `cancel` applies itself in its clause body
    cancel-step : (b : Bool) (q q' : Q) (c : Alphabet) (u₁ u z : String)
      → (c ∷ u₁) Eq.≡ u
      → (Trace b (δ q c) (u₁ ++ z) → Trace b q' z)
      → Trace b q (u ++ z) → Trace b q' z
    cancel-step b q q' c u₁ .(c ∷ u₁) z Eq.refl kont (roll ._ (stop p , x)) =
      Empty.rec (L.¬nil≡cons (Eq.eqToPath (x .lower .snd .fst)))
    cancel-step b q q' c u₁ .(c ∷ u₁) z Eq.refl kont (roll ._ (step d , ns , e , g)) =
      fin d (ns (suc zero))
        (flatEq d (ns zero) (ns (suc zero)) (c ∷ (u₁ ++ z)) (g zero .lower) e)
        (g (suc zero) .lower)
      where
      fin : (d' : Alphabet) (v : String)
        → (d' ∷ v) Eq.≡ (c ∷ (u₁ ++ z))
        → Trace b (δ q d') v → Trace b q' z
      fin .c .(u₁ ++ z) Eq.refl t' = kont t'

  cancel : (b : Bool) (q q' : Q) (u z : String)
    → TraceTo q q' u → Trace b q (u ++ z) → Trace b q' z
  cancel b q q' u z (roll .u (stop p , x)) =
    cancel-stop b q q' u z p (x .lower .snd .fst)
  cancel b q q' u z (roll .u (step c , ms , e , f)) =
    cancel-step b q q' c (ms (suc zero)) u z
      (flatEq c (ms zero) (ms (suc zero)) u (f zero .lower) e)
      (cancel b (δ q c) q' (ms (suc zero)) z (f (suc zero) .lower))

  -- The greedy answer, with maximality typed.

  Match : Q → Q → TheoryTy _ tt
  Match q q' = ⊕[ _ ∈ true Eq.≡ isAcc q' ] TraceTo q q'

  GreedyMax : Q → Q → TheoryTy _ tt
  GreedyMax q q' = Match q q' ⊗ ¬Ty ((L q' & char⁺) ⊗ ⊤Ty)

  Run : Q → TheoryTy _ tt
  Run q = (⊕[ q' ∈ Q ] GreedyMax q q') ⊕ ¬Ty (L q ⊗ ⊤Ty)

  Table : TheoryTy _ tt
  Table = &[ q ∈ Q ] Run q

  private
    -- a state rejecting ε has no empty run
    accN : (q : Q) → isAcc q Eq.≡ false → ¬Nullable (L q)
    accN q p = ¬Nullable-map (unrollTrace true q)
      (⊕-¬Nullable
        (⊕ᴰ-¬Nullable λ c → ⊗-¬Nullable (literal-¬Nullable c))
        (⊕ᴰ-¬Nullable λ pp → Empty.rec (true≢false (Eq.eqToPath (pp Eq.∙ p)))))

    accHere : (q : Q) → isAcc q Eq.≡ true → εTy ⊢ Match q q
    accHere q p = σ⊕ (Eq.sym p) ∘⊢ STOPTo q ∘⊢ liftTy

    noExt-ε : (R : TheoryTy ℓL tt) → εTy ⊢ ¬Ty ((R & char⁺) ⊗ ⊤Ty)
    noExt-ε R = ¬Nullable→¬ε (⊗-¬Nullable (&-¬NullableR char⁺-¬Nullable))

  scan-nil : εTy ⊢ Table
  scan-nil = &ᴰ-intro λ q → emptyRunAt q (isAcc q) Eq.refl
    where
    emptyRunAt : (q : Q) (b : Bool) → isAcc q Eq.≡ b → εTy ⊢ Run q
    emptyRunAt q true p =
      inl ∘⊢ σ⊕ q ∘⊢ (accHere q p ,⊗ noExt-ε (L q)) ∘⊢ ε⊗-intro
    emptyRunAt q false p = inr ∘⊢ ¬Nullable→¬ε (⊗-¬Nullable (accN q p))

  -- A dead successor is refuted without reading the table.
  --
  -- `dead-empty` says `Trace true q` is uninhabited, which is exactly the
  -- hypothesis `unmatched` wants -- so a dead `δ q c` answers with no `π`
  -- on the tail at all.  That is the early exit: forcing the tail's cell
  -- is what makes one token cost the whole remaining input.
  deadNo : (D : Deadness M) (q : Q)
    → Deadness.isDead D q Eq.≡ true → ⊤Ty ⊢ ¬Ty (L q ⊗ ⊤Ty)
  deadNo D q d m _ (ms , _ , t , _) =
    Empty.rec (dead-empty M D q d (ms zero) t)

  scan-cons : Deadness M → char ⊗ Table ⊢ Table
  scan-cons D = &ᴰ-intro λ q → ⊕ᴰ-elim (λ c → stepAt q c) ∘⊢ ⊗⊕ᴰ-distL
    where
    open Deadness D using (isDead)

    stepAt : (q : Q) (c : Alphabet) → literal c ⊗ Table ⊢ Run q
    stepAt q c = alive (isDead (δ q c)) Eq.refl
      where
      -- extending the match is one `STEP`, and no derivative
      extMatch : (q' : Q) → literal c ⊗ Match (δ q c) q' ⊢ Match q q'
      extMatch q' = ⊕ᴰ-elim (λ p → σ⊕ p ∘⊢ STEPTo c q q') ∘⊢ ⊗⊕ᴰ-distR

      matched : literal c ⊗ (⊕[ q' ∈ Q ] GreedyMax (δ q c) q') ⊢ Run q
      matched =
        inl ∘⊢ ⊕ᴰ-elim (λ q' → σ⊕ q' ∘⊢ (extMatch q' ,⊗ id⊢) ∘⊢ ⊗-assoc⁻)
        ∘⊢ ⊗⊕ᴰ-distR

      unmatched : literal c ⊗ ¬Ty (L (δ q c) ⊗ ⊤Ty) ⊢ Run q
      unmatched = onAcceptance (isAcc q) Eq.refl
        where
        δ-⊸⁻ : literal c ⊸ L q ⊢ L (δ q c)
        δ-⊸⁻ = ∂→Trace true q c ∘⊢ ⊸→∂⌈⌉ (⌈gen c ⌉) {B = L q}

        noMore : literal c ⊗ ¬Ty (L (δ q c) ⊗ ⊤Ty)
          ⊢ ¬Ty ((L q & char⁺) ⊗ ⊤Ty)
        noMore = noExt-step c ∘⊢ (id⊢ ,⊗ ¬Ty-map (δ-⊸⁻ ,⊗ id⊢))

        onAcceptance : (b : Bool) → isAcc q Eq.≡ b
                     → literal c ⊗ ¬Ty (L (δ q c) ⊗ ⊤Ty) ⊢ Run q
        onAcceptance true p =
          inl ∘⊢ σ⊕ q ∘⊢ (accHere q p ,⊗ id⊢) ∘⊢ ε⊗-intro ∘⊢ noMore
        onAcceptance false p =
          inr ∘⊢ ¬Ty-map ((id⊢ ,& ¬Nullable→char⁺ (accN q p)) ,⊗ id⊢) ∘⊢ noMore

      alive : (b : Bool) → isDead (δ q c) Eq.≡ b
        → literal c ⊗ Table ⊢ Run q
      alive true p = unmatched ∘⊢ (id⊢ ,⊗ (deadNo D (δ q c) p ∘⊢ ⊤Ty-intro))
      alive false _ =
        ⊕-elim matched unmatched ∘⊢ ⊗⊕-distR ∘⊢ (id⊢ ,⊗ π (δ q c))

  module _ (isSetQ : isSet Q) where
    private
      isSetTagTo : (q q' : Q) → isSet (TagTo q' q)
      isSetTagTo q q' = isSetRetract to from ret
        (isSet⊎ (isProp→isSet (isSet→isSetEq isSetQ)) isSetAlphabet)
        where
        to : TagTo q' q → (q Eq.≡ q') ⊎ Alphabet
        to (stop p) = Sum.inl p
        to (step c) = Sum.inr c

        from : (q Eq.≡ q') ⊎ Alphabet → TagTo q' q
        from (Sum.inl p) = stop p
        from (Sum.inr c) = step c

        ret : (t : TagTo q' q) → from (to t) ≡ t
        ret (stop p) = refl
        ret (step c) = refl

      codeIsSetTo : (q' q : Q) → isSetValued (TraceToTy q' q)
      codeIsSetTo q' q .fst = lift (isSetTagTo q q')
      codeIsSetTo q' q .snd (stop _) = lift (isSet⊗ ε· _ _ λ ())
      codeIsSetTo q' q .snd (step c) zero =
        lift λ m → isProp→isSet isPropEqString
      codeIsSetTo q' q .snd (step c) (suc zero) = lift tt*

    isSetTraceTo : (q q' : Q) → isSetTheoryTy (TraceTo q q')
    isSetTraceTo q q' = isSetμ (TraceToTy q') (codeIsSetTo q') q

    private
      isSet⊗bin : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
        → isSetTheoryTy A → isSetTheoryTy B → isSetTheoryTy (A ⊗ B)
      isSet⊗bin sA sB = isSet⊗ _⊙_ _ _ λ where
        zero → sA
        (suc zero) → sB

      isSetMatch : (q q' : Q) → isSetTheoryTy (Match q q')
      isSetMatch q q' =
        isSet⊕ᴰ (isProp→isSet (isSet→isSetEq isSetBool))
          λ _ → isSetTraceTo q q'

      isSetTable : isSetTheoryTy Table
      isSetTable = isSet&ᴰ λ q → isSet⊕
        (isSet⊕ᴰ isSetQ λ q' →
          isSet⊗bin (isSetMatch q q') λ m → isProp→isSet (isProp¬Ty _))
        (λ m → isProp→isSet (isProp¬Ty _))

    scan : Deadness M → char * ⊢ Table
    scan D = fold*g (Table , isSetTable) char-¬Nullable scan-nil (scan-cons D)

    -- The bridge is an iso by `Automaton/Unambiguous`'s induction, with
    -- the acceptance equation replaced by the end-state equation.
    -- Together with `endState` -- which says the `⊕[ q' ]` of `BridgeTy`
    -- is a singleton -- it makes `BridgeTy b q` a proposition, and two
    -- propositions with maps both ways are isomorphic.

    unambiguous-TraceTo : (q q' : Q) (w : String)
      (t t' : TraceTo q q' w) → t ≡ t'
    unambiguous-TraceTo q q' w
      (roll .w (stop p , x)) (roll .w (stop p' , x')) =
      cong (roll w)
        (ΣPathP
          ( cong TagTo.stop (isSet→isSetEq isSetQ p p')
          , isPropPathP _ (isOfHLevelLift 1 (isPropεTy w)) x x'))
    unambiguous-TraceTo q q' w
      (roll .w (stop p , x)) (roll .w (step d , ns , e' , f')) =
      Empty.rec (lit⊗-nil d (ns zero) (ns (suc zero))
                   (f' zero .lower)
                   (e' Eq.∙ Eq.sym (x .lower .snd .fst)))
    unambiguous-TraceTo q q' w
      (roll .w (step c , ms , e , f)) (roll .w (stop p' , x')) =
      Empty.rec (lit⊗-nil c (ms zero) (ms (suc zero))
                   (f zero .lower)
                   (e Eq.∙ Eq.sym (x' .lower .snd .fst)))
    unambiguous-TraceTo q q' w
      (roll .w (step c , ms , e , f)) (roll .w (step d , ns , e' , f')) =
      -- the recursive call stands in the clause body, as in `Unambiguous`
      main (unambiguous-TraceTo (δ q d) q' (ns (suc zero))
             (transport (λ i → Fam i) (f (suc zero) .lower))
             (f' (suc zero) .lower))
      where
      heads : c ∷ ms (suc zero) ≡ d ∷ ns (suc zero)
      heads = flat c (ms zero) (ms (suc zero)) w (f zero .lower) e
            ∙ sym (flat d (ns zero) (ns (suc zero)) w (f' zero .lower) e')

      c≡d : c ≡ d
      c≡d = L.cons-inj₁ heads

      sp : ms ≡ ns
      sp = funExt λ where
        zero →
          Eq.eqToPath (f zero .lower)
          ∙ cong (_∷ []) c≡d
          ∙ sym (Eq.eqToPath (f' zero .lower))
        (suc zero) → L.cons-inj₂ heads

      eqP : PathP (λ i → op _⊙_ (sp i) Eq.≡ w) e e'
      eqP = isProp→PathP (λ i → isPropEqString) e e'

      Fam : I → Type (ℓ-max (ℓF ℓM) ℓAlph)
      Fam i = TraceTo (δ q (c≡d i)) q' (sp i (suc zero))

      main : transport (λ i → Fam i) (f (suc zero) .lower)
             ≡ f' (suc zero) .lower
           → roll w (step c , ms , e , f) ≡ roll w (step d , ns , e' , f')
      main h =
        cong (roll w)
          (ΣPathP (cong (TagTo.step {q'} {q}) c≡d
                  , λ i → sp i , eqP i , λ α → gP α i))
        where
        tP : PathP Fam (f (suc zero) .lower) (f' (suc zero) .lower)
        tP = toPathP h

        gP : (α : Fin 2)
          → PathP (λ i → ⟦ two (k (literal (c≡d i))) (Var (δ q (c≡d i))) α ⟧TheoryTy
                           (μ (TraceToTy q')) (sp i α))
              (f α) (f' α)
        gP zero =
          isPropPathP _ (isOfHLevelLift 1 isPropEqString) (f zero) (f' zero)
        gP (suc zero) = λ i → lift (tP i)

    -- the end state is determined, the acceptance equation is a
    -- proposition, and the trace is unambiguous
    isPropBridgeTy : (b : Bool) (q : Q) (m : String) → isProp (BridgeTy b q m)
    isPropBridgeTy b q m (q₁ , p₁ , t₁) (q₂ , p₂ , t₂) =
      ΣPathP (qp , ΣPathP (pp , tp))
      where
      qp : q₁ ≡ q₂
      qp = sym (Eq.eqToPath (endState q q₁ m t₁))
         ∙ Eq.eqToPath (endState q q₂ m t₂)

      pp : PathP (λ i → b Eq.≡ isAcc (qp i)) p₁ p₂
      pp = isProp→PathP (λ i → isSet→isSetEq isSetBool) p₁ p₂

      tp : PathP (λ i → TraceTo q (qp i) m) t₁ t₂
      tp = toPathP (unambiguous-TraceTo q q₂ m _ t₂)

    bridge-retract : (b : Bool) (q : Q)
      → Trace→TraceTo b q ∘⊢ bridge b q ≡ id⊢
    bridge-retract b q =
      funExt λ m → funExt λ s → isPropBridgeTy b q m _ s

    Trace≅TraceTo : (b : Bool) (q : Q) (m : String)
      → Iso (BridgeTy b q m) (Trace b q m)
    Trace≅TraceTo b q m .Iso.fun = bridge b q m
    Trace≅TraceTo b q m .Iso.inv = Trace→TraceTo b q m
    Trace≅TraceTo b q m .Iso.sec t = unambiguous-Trace M b q m _ t
    Trace≅TraceTo b q m .Iso.ret s = isPropBridgeTy b q m _ s

  -- The state-indexed witness maps into the word-indexed `Greedy` of
  -- `Greedy/Base`.  `cancel` is the whole content: it turns a run of `q`
  -- over `u ++ z` into a run of `q'` over `z`, where the refutation of
  -- every nonempty extension already lives.

  GreedyMax→Greedy : (q : Q) → (⊕[ q' ∈ Q ] GreedyMax q q') ⊢ Greedy (L q)
  GreedyMax→Greedy q = ⊕ᴰ-elim body
    where
    body : (q' : Q) → GreedyMax q q' ⊢ Greedy (L q)
    body q' m (ms , e , ((p , t) , (nk , _))) =
      ms zero
      , ( ms , e
        , ( (Eq.refl , TraceTo→Trace true q q' p (ms zero) t)
          , (ext , tt*)))
      where
      ext : ¬Ty (((⌈ ms zero ⌉ ⊸ L q) & char⁺) ⊗ ⊤Ty) (ms (suc zero))
      ext (ns , e' , (y , (top , _))) =
        nk ( ns , e'
           , ( ( cancel true q q' (ms zero) (ns zero) t
                   (y .fst (ms zero) Eq.refl)
               , y .snd)
             , (top , tt*)))

  Run→Greedy : (q : Q) → Run q ⊢ Greedy (L q) ⊕ ¬Ty (L q ⊗ ⊤Ty)
  Run→Greedy q = ⊕-elim (inl ∘⊢ GreedyMax→Greedy q) inr

  no-longer-match : (q q' : Q) (u z r : String)
    → TraceTo q q' u                        -- the match, ending at `q'`
    → ¬Ty ((L q' & char⁺) ⊗ ⊤Ty) (z ++ r)   -- its refutation
    → char⁺ z                               -- a nonempty extension
    → L q (u ++ z)                          -- also accepted from `q`
    → ⊥Ty (z ++ r)
  no-longer-match q q' u z r t nk cz acc =
    nk (two z r , Eq.refl
       , ((cancel true q q' u z t acc , cz) , (tt , tt*)))
