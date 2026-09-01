{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The token stream as a grammar, and its decision; `&` shares the right
   factor between continuation and maximality refutation:

     StreamF X = εTy ⊕ (⊕[ q' ] Match (init) q' ⊗ (NoExt q' & X))

   Well-founded: a greedy match jumps a non-empty token (`PayR`). -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Automaton.TokenStream
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool ; true≢false)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.FinData.Properties using (isSetFin)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.List.Properties using (cons-inj₁ ; cons-inj₂)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit* ; tt ; tt* ; isSetUnit*)
open import Cubical.Data.Sum as Sum using (_⊎_ ; isSet⊎)
import Cubical.Data.Empty as Empty
import Cubical.Data.Maybe as Mb
import Cubical.Data.Equality as Eq
open import Cubical.Data.Equality.More using (isSet→isSetEq)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet
  using (_* ; readChars ; unroll↑)
open import Theory.Instances.Monoid.KleeneStar.Guarded Alphabet isSetAlphabet
  using (¬Nullable ; ¬Nullable→NonNull ; ⊗-¬Nullable ; ⊕-¬Nullable
       ; literal-¬Nullable ; char-¬Nullable)
open import Theory.Instances.Monoid.Greedy.Base Alphabet isSetAlphabet
  using (char⁺)
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (&⊕-distR)
open import Theory.Instances.Monoid.Convolution Alphabet isSetAlphabet
  using (⟦⊗e⟧ ; ⟦⊗e⟧⁻)
open import Theory.Instances.Monoid.SemanticAction Alphabet isSetAlphabet
  using (SemanticAction ; observe ; semact-pure ; semact-rec ; semact-dec)
import Theory.Instances.Monoid.SemanticAction Alphabet isSetAlphabet as Act
open import Theory.Instances.Monoid.Automaton.Deterministic
  Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Greedy Alphabet isSetAlphabet
  using (¬Nullable-map ; ⊕ᴰ-¬Nullable)
open import Theory.Instances.Monoid.Automaton.GreedyMax Alphabet isSetAlphabet
  using (Match ; GreedyMax ; Run ; Table ; scan-nil ; scan-cons
       ; bridge ; isSetTraceTo ; no-longer-match)
open import Theory.Instances.Monoid.Automaton.Lexicon Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Lookahead.Base Alphabet isSetAlphabet
  using (dec-ε)
open import Theory.Instances.Monoid.Suffix.Base Alphabet isSetAlphabet
  using (module Guarded▷ ; Below)
open import Theory.Type.Guarded.Base MonEqns Alphabet (λ _ → tt)
  listPresentation using (Löb)
open import Theory.Instances.Monoid.GuardedSplit MonEqns Alphabet (λ _ → tt)
  listPresentation using (PayR ; ▷⊛r)
open import Theory.Instances.Monoid.Phase Alphabet isSetAlphabet using (Phase)
open import Theory.Type.Decidable.Base MonEqns Alphabet (λ _ → tt)
  listPresentation
open import Theory.Type.HLevels MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Inductive.HLevels MonEqns Alphabet (λ _ → tt)
  listPresentation

private variable ℓA ℓB : Level

open DeterministicAutomaton

private
  splitCmp : (u z u' z' : String) → (u ++ z) ≡ (u' ++ z')
    → (Σ[ y ∈ String ] ((u' ≡ u ++ y) × (z ≡ y ++ z')))
    ⊎ (Σ[ y ∈ String ] ((u ≡ u' ++ y) × (z' ≡ y ++ z)))
  splitCmp [] z u' z' p = Sum.inl (u' , refl , p)
  splitCmp (c ∷ u) z [] z' p = Sum.inr (c ∷ u , refl , sym p)
  splitCmp (c ∷ u) z (d ∷ u') z' p =
    Sum.rec
      (λ r → Sum.inl (r .fst , cong₂ _∷_ (sym hd) (r .snd .fst) , r .snd .snd))
      (λ r → Sum.inr (r .fst , cong₂ _∷_ hd (r .snd .fst) , r .snd .snd))
      (splitCmp u z u' z' (cons-inj₂ p))
    where
    hd : c ≡ d
    hd = cons-inj₁ p

  char⁺-cons : (c : Alphabet) (y : String) → char⁺ (c ∷ y)
  char⁺-cons c y =
    two (c ∷ []) y , Eq.refl , ((c , Eq.refl) , (read y tt , tt*))

module Stream {n : ℕ} (Qs : Fin n → Type ℓAlph)
  (Ms : (i : Fin n) → DeterministicAutomaton (Qs i))
  (Ds : (i : Fin n) → Deadness (Ms i))
  (sQ : (i : Fin n) → isSet (Qs i)) where

  open Product Qs Ms Ds sQ public

  private
    q₀ : ProdQ
    q₀ = init Prod

    L : ProdQ → TheoryTy _ tt
    L q = Trace Prod true q

  -- no longer match is possible from the state the greedy match ended in
  NoExt : ProdQ → TheoryTy _ tt
  NoExt q' = ¬Ty ((L q' & char⁺) ⊗ ⊤Ty)

  -- the tag carries the winning rule, so tokenisation lives in the parse tree
  data StreamTag : Type ℓAlph where
    nilT : StreamTag
    tokT : (q' : ProdQ) → Wins q' → StreamTag

  SIx : Type ℓAlph
  SIx = Unit* {ℓAlph}

  StreamF : Functor (ℓF ℓM) SIx (λ _ → tt) tt
  StreamF = ⊕e StreamTag λ where
    nilT → k (LiftTheoryTy (ℓF ℓM) εTy)
    (tokT q' _) →
      ⊗e _⊙_ (two (k (Match Prod q₀ q')) (k (NoExt q') &e2 Var tt*))

  TokStream : TheoryTy _ tt
  TokStream = μ (λ _ → StreamF) tt*

  NILs : εTy ⊢ TokStream
  NILs = roll ∘⊢ σ⊕ {Y = StreamTag} nilT ∘⊢ liftTy ∘⊢ liftTy

  CONSs : (q' : ProdQ) (w : Wins q')
    → Match Prod q₀ q' ⊗ (NoExt q' & TokStream) ⊢ TokStream
  CONSs q' w = roll ∘⊢ σ⊕ {Y = StreamTag} (tokT q' w) ∘⊢ branch
    where
    branch : Match Prod q₀ q' ⊗ (NoExt q' & TokStream)
      ⊢ ⟦ ⊗e _⊙_ (two (k (Match Prod q₀ q')) (k (NoExt q') &e2 Var tt*))
          ⟧TheoryTy (μ (λ _ → StreamF))
    branch = ⟦⊗e⟧⁻ _ _ ∘⊢ ⊗-map liftTy (liftTy ,&p liftTy)

  -- one layer, as a sum of connectives rather than a code
  StreamLayer : TheoryTy _ tt
  StreamLayer =
    εTy ⊕ (⊕[ t ∈ Σ[ q' ∈ ProdQ ] Wins q' ]
            (Match Prod q₀ (t .fst) ⊗ (NoExt (t .fst) & TokStream)))

  unrollStream : TokStream ⊢ StreamLayer
  unrollStream = fromF ∘⊢ unroll (λ _ → StreamF) tt*
    where
    fromF : ⟦ StreamF ⟧TheoryTy (μ (λ _ → StreamF)) ⊢ StreamLayer
    fromF = ⊕ᴰ-elim λ where
      nilT → inl ∘⊢ lowerTy ∘⊢ lowerTy
      (tokT q' w) →
        inr ∘⊢ σ⊕ (q' , w)
        ∘⊢ ⊗-map lowerTy (lowerTy ,&p lowerTy) ∘⊢ ⟦⊗e⟧ _ _

  emitStream : SemanticAction TokStream (List (Fin n × String))
  emitStream = semact-rec alg tt*
    where
    Out : Type ℓM
    Out = List (Fin n × String)

    consAct : (q' : ProdQ) (w : Wins q')
      → ⟦ ⊗e _⊙_ (two (k (Match Prod q₀ q')) (k (NoExt q') &e2 Var tt*))
          ⟧TheoryTy (λ _ → Act.Δ Out) ⊢ Act.Δ Out
    consAct q' w m x =
      ((winsIdx q' w , semact-text {A = Match Prod q₀ q'} (x .fst zero)
          (x .snd .snd zero .lower) .fst)
        ∷ x .snd .snd (suc zero) .snd .lower .fst)
      , tt

    alg : (x : SIx) → ⟦ StreamF ⟧TheoryTy (λ _ → Act.Δ Out) ⊢ Act.Δ Out
    alg _ = ⊕ᴰ-elim λ where
      nilT → semact-pure []
      (tokT q' w) → consAct q' w

  private
    matchToL : (q' : ProdQ) → Match Prod q₀ q' ⊢ L q₀
    matchToL q' = bridge Prod true q₀ ∘⊢ σ⊕ q'

    streamShape : TokStream ⊢ εTy ⊕ (L q₀ ⊗ ⊤Ty)
    streamShape =
      ⊕-elim inl
        (inr ∘⊢ ⊕ᴰ-elim (λ t → matchToL (t .fst) ,⊗ ⊤Ty-intro))
      ∘⊢ unrollStream

  -- side condition: no lexicon rule accepts ε, else a token may be empty
  module _ (q₀-rejects-ε : isAcc Prod q₀ Eq.≡ false) where
    private
      -- restates `Automaton/Greedy.accN` (private there)
      initNN : ¬Nullable (L q₀)
      initNN = ¬Nullable-map (unrollTrace Prod true q₀)
        (⊕-¬Nullable
          (⊕ᴰ-¬Nullable λ c → ⊗-¬Nullable (literal-¬Nullable c))
          (⊕ᴰ-¬Nullable λ pp →
            Empty.rec (true≢false (Eq.eqToPath (pp Eq.∙ q₀-rejects-ε)))))

      matchNN : (q' : ProdQ) → ¬Nullable (Match Prod q₀ q')
      matchNN q' = ¬Nullable-map (matchToL q') initNN

      isSetWins : (f : ProdQ) → isSet (Wins f)
      isSetWins f = isSetΣ isSetFin λ i →
        isSet× (isProp→isSet (isSetBool _ _))
          (isSetΠ λ j → isSetΠ λ _ → isProp→isSet (isSetBool _ _))

      isSetStreamTag : isSet StreamTag
      isSetStreamTag = isSetRetract to from ret
        (isSet⊎ isSetUnit* (isSetΣ isSetProdQ isSetWins))
        where
        to : StreamTag → Unit* {ℓ-zero} ⊎ (Σ[ q' ∈ ProdQ ] Wins q')
        to nilT = Sum.inl tt*
        to (tokT q' w) = Sum.inr (q' , w)

        from : Unit* {ℓ-zero} ⊎ (Σ[ q' ∈ ProdQ ] Wins q') → StreamTag
        from (Sum.inl _) = nilT
        from (Sum.inr t) = tokT (t .fst) (t .snd)

        ret : (t : StreamTag) → from (to t) ≡ t
        ret nilT = refl
        ret (tokT q' w) = refl

      -- `GreedyMax`'s own `isSetMatch`/`isSetTable` are private there
      isSetMatchAt : (q q' : ProdQ) → isSetTheoryTy (Match Prod q q')
      isSetMatchAt q q' =
        isSet⊕ᴰ (isProp→isSet (isSet→isSetEq isSetBool))
          λ _ → isSetTraceTo Prod isSetProdQ q q'

      isSetMatch : (q' : ProdQ) → isSetTheoryTy (Match Prod q₀ q')
      isSetMatch = isSetMatchAt q₀

      isSetTable : isSetTheoryTy (Table Prod)
      isSetTable = isSet&ᴰ λ q → isSet⊕
        (isSet⊕ᴰ isSetProdQ λ q' →
          isSet⊗2 (isSetMatchAt q q')
            λ m → isProp→isSet (isProp¬Ty ((L q' & char⁺) ⊗ ⊤Ty)))
        (λ m → isProp→isSet (isProp¬Ty (L q ⊗ ⊤Ty)))

      codeIsSet : (x : SIx) → isSetValued StreamF
      codeIsSet _ .fst = lift isSetStreamTag
      codeIsSet _ .snd nilT = lift (isSetLiftTheoryTy (isSet⊗ ε· _ _ λ ()))
      codeIsSet _ .snd (tokT q' w) zero = lift (isSetMatch q')
      codeIsSet _ .snd (tokT q' w) (suc zero) .fst =
        lift λ m → isProp→isSet (isProp¬Ty ((L q' & char⁺) ⊗ ⊤Ty))
      codeIsSet _ .snd (tokT q' w) (suc zero) .snd = lift tt*

      isSetTokStream : isSetTheoryTy TokStream
      isSetTokStream = isSetμ (λ _ → StreamF) codeIsSet tt*

      DecStream : TheoryTy _ tt
      DecStream = DecTy TokStream

      isSetDecStream : isSetTheoryTy DecStream
      isSetDecStream =
        isSet⊕ isSetTokStream λ m → isProp→isSet (isProp¬Ty TokStream)

      -- carrying `scan`'s table per suffix makes it a memo cell: no token
      -- boundary restarts the fold
      Carrier : TheoryTy _ tt
      Carrier = Table Prod & DecStream

      isSetCarrier : isSetTheoryTy Carrier
      isSetCarrier = isSet& isSetTable isSetDecStream

    -- measured (x-token stream, 38..1280 tokens): plain löb within 8% of the
    -- tabulated one at every scale — the memo hypothesis did not survive
    -- benchmarking, so the simple Löb is the one in use
    module DecideWith (theLöb : Löb Below (λ _ → Carrier)) where
      private module GD = Löb theLöb
  
      private
        -- maximal munch is unique: this match and a rival's prefix the same
        -- word, so one extends the other, and `NoExt` refutes extensions
        refuteExt : (q' : ProdQ)
          → Match Prod q₀ q' ⊗ (NoExt q' & ¬Ty TokStream) ⊢ ¬Ty TokStream
        refuteExt q' m gm t = go t
          where
          u z : String
          u = gm .fst zero
          z = gm .fst (suc zero)
  
          eu : (u ++ z) Eq.≡ m
          eu = gm .snd .fst
  
          mt : Match Prod q₀ q' u
          mt = gm .snd .snd .fst
  
          nk : NoExt q' z
          nk = gm .snd .snd .snd .fst .fst
  
          nrest : ¬Ty TokStream z
          nrest = gm .snd .snd .snd .fst .snd
  
          rival : (q'' : ProdQ)
            → (Match Prod q₀ q'' ⊗ (NoExt q'' & TokStream)) m → ⊥Ty m
          rival q'' r = branch (splitCmp u z u'' z'' agree)
            where
            u'' z'' : String
            u'' = r .fst zero
            z'' = r .fst (suc zero)
  
            mt'' : Match Prod q₀ q'' u''
            mt'' = r .snd .snd .fst
  
            nk'' : NoExt q'' z''
            nk'' = r .snd .snd .snd .fst .fst
  
            t'' : TokStream z''
            t'' = r .snd .snd .snd .fst .snd
  
            agree : (u ++ z) ≡ (u'' ++ z'')
            agree = Eq.eqToPath eu ∙ sym (Eq.eqToPath (r .snd .fst))
  
            longer : (y : String) → u'' ≡ (u ++ y) → z ≡ (y ++ z'') → ⊥Ty m
            longer [] pu pz =
              nrest (subst TokStream (sym pz) t'')
            longer (c ∷ y) pu pz =
              no-longer-match Prod q₀ q' u (c ∷ y) z'' (mt .snd)
                (subst (NoExt q') pz nk)
                (char⁺-cons c y)
                (subst (L q₀) pu (matchToL q'' u'' mt''))
  
            shorter : (y : String) → u ≡ (u'' ++ y) → z'' ≡ (y ++ z) → ⊥Ty m
            shorter [] pu pz = nrest (subst TokStream pz t'')
            shorter (c ∷ y) pu pz =
              no-longer-match Prod q₀ q'' u'' (c ∷ y) z (mt'' .snd)
                (subst (NoExt q'') pz nk'')
                (char⁺-cons c y)
                (subst (L q₀) pu (matchToL q' u mt))
  
            branch :
              (Σ[ y ∈ String ] ((u'' ≡ u ++ y) × (z ≡ y ++ z'')))
              ⊎ (Σ[ y ∈ String ] ((u ≡ u'' ++ y) × (z'' ≡ y ++ z)))
              → ⊥Ty m
            branch (Sum.inl s) = longer (s .fst) (s .snd .fst) (s .snd .snd)
            branch (Sum.inr s) = shorter (s .fst) (s .snd .fst) (s .snd .snd)
  
          go : TokStream m → ⊥Ty m
          go s = Sum.rec
            (λ eps → ⊗-¬Nullable (matchNN q') m (gm , eps))
            (λ r → rival (r .fst .fst) (r .snd))
            (unrollStream m s)
  
        pay : (q' : ProdQ) → PayR theLöb {X = Match Prod q₀ q'}
        pay q' = ¬Nullable→NonNull (matchNN q')
  
        -- hypothesis read at the rest, put strictly below by the payment
        atTok : (q' : ProdQ) (w : Wins q')
          → GreedyMax Prod q₀ q' & GD.▷ tt ⊢ DecStream
        atTok q' w =
          ⊕-elim (dec-yes ∘⊢ CONSs q' w) (dec-no ∘⊢ refuteExt q')
          ∘⊢ ⊗⊕-distR
          ∘⊢ (id⊢ ,⊗ &⊕-distR)
          ∘⊢ (id⊢ ,⊗ (id⊢ ,&p π₂))
          ∘⊢ ▷⊛r theLöb (pay q')
  
        tokBranch : GD.▷ tt & Tok ⊢ DecStream
        tokBranch =
          ⊕ᴰ-elim (λ q' → ⊕ᴰ-elim (λ w → atTok q' w) ∘⊢ &⊕ᴰ-distL)
          ∘⊢ &⊕ᴰ-distL ∘⊢ &-swap
  
        noneBranch : GD.▷ tt & ¬Ty (L q₀ ⊗ ⊤Ty) ⊢ DecStream
        noneBranch =
          ⊕-elim& (dec-yes ∘⊢ NILs ∘⊢ π₂)
                  (dec-no ∘⊢ ¬Ty-map streamShape ∘⊢ ¬-⊕ ∘⊢ &-swap)
          ∘⊢ (id⊢ ,& (dec-ε ∘⊢ ⊤Ty-intro))
          ∘⊢ π₂
  
        -- a letter pays for the rest; `scan-cons` is the whole step
        payChar : PayR theLöb {X = char}
        payChar = ¬Nullable→NonNull char-¬Nullable
  
        tblCons : GD.▷ tt & (char ⊗ (char *)) ⊢ Table Prod
        tblCons =
          scan-cons Prod ProdDead
          ∘⊢ (id⊢ ,⊗ (π₁ ∘⊢ π₂))
          ∘⊢ ▷⊛r theLöb payChar
          ∘⊢ &-swap
  
        tbl : GD.▷ tt ⊢ Table Prod
        tbl =
          ⊕-elim& tblCons (scan-nil Prod ∘⊢ π₂)
          ∘⊢ (id⊢ ,& (unroll↑ ∘⊢ readChars ∘⊢ ⊤Ty-intro))
  
        -- decision off the table: no scan is restarted
        decPart : GD.▷ tt & Table Prod ⊢ DecStream
        decPart =
          ⊕-elim& tokBranch noneBranch
          ∘⊢ (π₁ ,& (lexOne ∘⊢ π q₀ ∘⊢ π₂))
  
        -- table built once, read twice: threaded through the pair
        decStep : GD.▷ tt ⊢ Carrier
        decStep = (π₂ ,& decPart) ∘⊢ (id⊢ ,& tbl)
  
      decideStream : Decidable TokStream
      decideStream = π₂ ∘⊢ GD.löb (λ _ → decStep) tt

    decideStream : Decidable TokStream
    decideStream = DecideWith.decideStream
      (Guarded▷.suffixLöb (λ _ → Carrier) (λ _ → isSetCarrier))

    lexPhase : Phase _ (Fin n × String)
    lexPhase .Phase.Gr = TokStream
    lexPhase .Phase.dec = decideStream
    lexPhase .Phase.emit = emitStream

    tokeniseS : String → Mb.Maybe (List (Fin n × String))
    tokeniseS = observe decideStream (semact-dec emitStream)

-- COST: linear.  `Deadness.dead-empty` lets `scan-cons` refute a dead
-- successor without forcing the tail's cell; `Lexicon.Tup` makes the
-- product state a pair, forced once instead of per character.
-- Measured vs a baseline building the five POSIX rules and tokenising
-- nothing (marginal seconds, `x ` repeated):
--
--     tokens:    40    80   160   320   640
--     before:  0.91  4.25 20.51     -     -
--      after:  0.16  0.29  0.54  1.06  2.04
