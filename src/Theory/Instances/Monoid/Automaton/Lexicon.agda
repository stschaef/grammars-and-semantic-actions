{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A lexicon: several token rules, longest match across all of them,
   ties broken by rule priority.

   A lexicon is *not* `⊕Aut` of its rules.  That construction wants the
   rules' first sets disjoint, and a lexicon deliberately overlaps --
   `where` is also an identifier -- and resolves the overlap by priority.

   So run every rule at once instead: the state is a tuple of the rules'
   states, `δ` steps each component, and the product accepts when *some*
   rule does.  `Tup Qs` keeps that at `ℓAlph`, so `Deterministic`'s
   `parse` and `GreedyMax`'s `scan` apply unchanged, and maximal munch
   over the product is longest match across the whole lexicon.  A product
   state is dead when every component is, which is what lets `scan` stop
   at the end of a token instead of at the end of the input.

   Priority is then a readout, not a construction: an accepting product
   state is a `Fin n → Bool`, and the winning rule is its least `true`.
   `find` returns that index together with its minimality. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Automaton.Lexicon
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Bool using (Bool ; true ; false ; _or_ ; _and_ ; true≢false)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order using (_<_ ; ¬-<-zero ; pred-≤-pred)
open import Cubical.Data.FinData using (Fin ; toℕ) renaming (zero to fz ; suc to fs)
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt ; Unit* ; tt* ; isSetUnit*)
import Cubical.Data.Maybe as Mb
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet
  using (readChars ; _*)
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⊗⊕ᴰ-distL)
open import Theory.Instances.Monoid.SemanticAction Alphabet isSetAlphabet
  using (SemanticAction ; observe ; semact-⊕ ; semact-⊕ᴰ' ; semact-map
       ; semact-pure ; semact-⊗₂ ; semact-string)
open import Theory.Instances.Monoid.Automaton.Deterministic
  Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Automaton.GreedyMax Alphabet isSetAlphabet
  using (TraceTo ; Match ; GreedyMax ; Run ; Table ; scan)
open import Theory.Type.Decidable.Base MonEqns Alphabet (λ _ → tt)
  listPresentation using (¬Ty)

private variable ℓA : Level

-- Priority, over `Fin n`.

-- "some rule accepts": the acceptance predicate of the product, and a
-- bare `Bool` fold so that stepping the product costs nothing.
anyFin : {n : ℕ} → (Fin n → Bool) → Bool
anyFin {n = zero} p = false
anyFin {n = suc n} p = p fz or anyFin (λ i → p (fs i))

anyFin-true : {n : ℕ} (p : Fin n → Bool) (i : Fin n)
  → p i ≡ true → anyFin p ≡ true
anyFin-true {n = suc n} p fz e = cong (_or anyFin (λ i → p (fs i))) e
anyFin-true {n = suc n} p (fs i) e =
  cong₂ _or_ (refl {x = p fz}) (anyFin-true (λ j → p (fs j)) i e)
  ∙ orTrue (p fz)
  where
  orTrue : (b : Bool) → (b or true) ≡ true
  orTrue true = refl
  orTrue false = refl

anyFin-false : {n : ℕ} (p : Fin n → Bool)
  → ((i : Fin n) → p i ≡ false) → anyFin p ≡ false
anyFin-false {n = zero} p h = refl
anyFin-false {n = suc n} p h =
  cong₂ _or_ (h fz) (anyFin-false (λ i → p (fs i)) (λ i → h (fs i)))

-- "every rule is dead": the product's deadness test, and its elimination
allFin : {n : ℕ} → (Fin n → Bool) → Bool
allFin {n = zero} p = true
allFin {n = suc n} p = p fz and allFin (λ i → p (fs i))

allFin-intro : {n : ℕ} (p : Fin n → Bool)
  → ((i : Fin n) → p i Eq.≡ true) → allFin p Eq.≡ true
allFin-intro {n = zero} p h = Eq.refl
allFin-intro {n = suc n} p h =
  Eq.transport (λ b → (b and allFin (λ i → p (fs i))) Eq.≡ true)
    (Eq.sym (h fz)) (allFin-intro (λ i → p (fs i)) (λ i → h (fs i)))

allFin-elim : {n : ℕ} (p : Fin n → Bool)
  → allFin p Eq.≡ true → (i : Fin n) → p i Eq.≡ true
allFin-elim p h fz = headTrue (p fz) Eq.refl
  where
  headTrue : (b : Bool) → p fz Eq.≡ b → p fz Eq.≡ true
  headTrue true e = e
  headTrue false e = Empty.rec (true≢false (sym (Eq.eqToPath h)
    ∙ cong (_and allFin (λ i → p (fs i))) (Eq.eqToPath e)))
allFin-elim p h (fs i) = allFin-elim (λ j → p (fs j)) rest i
  where
  rest : allFin (λ j → p (fs j)) Eq.≡ true
  rest = tailAll (p fz) Eq.refl
    where
    tailAll : (b : Bool) → p fz Eq.≡ b → allFin (λ j → p (fs j)) Eq.≡ true
    tailAll true e =
      Eq.transport (λ b → (b and allFin (λ j → p (fs j))) Eq.≡ true) e h
    tailAll false e = Empty.rec (true≢false (sym (Eq.eqToPath h)
      ∙ cong (_and allFin (λ j → p (fs j))) (Eq.eqToPath e)))

-- The readout, with its evidence: the least `true`, or a refutation of
-- every index.  Priority *is* this minimality.
Found : {n : ℕ} → (Fin n → Bool) → Type ℓ-zero
Found {n = n} p =
  (Σ[ i ∈ Fin n ] (p i ≡ true)
     × ((j : Fin n) → toℕ j < toℕ i → p j ≡ false))
  Sum.⊎ ((i : Fin n) → p i ≡ false)

find : {n : ℕ} (p : Fin n → Bool) → Found p
find {n = zero} p = Sum.inr λ ()
find {n = suc n} p = findFromHead (p fz) refl
  where
  findFromHead : (b : Bool) → p fz ≡ b → Found p
  findFromHead true e = Sum.inl (fz , e , λ j lt → Empty.rec (¬-<-zero lt))
  findFromHead false e = Sum.rec
    (λ x → Sum.inl (fs (x .fst) , x .snd .fst , least (x .fst) (x .snd .snd)))
    (λ h → Sum.inr λ where fz → e ; (fs i) → h i)
    (find (λ i → p (fs i)))
    where
    least : (i : Fin n)
      → ((j : Fin n) → toℕ j < toℕ i → p (fs j) ≡ false)
      → (j : Fin (suc n)) → toℕ j < toℕ (fs i) → p j ≡ false
    least i h fz lt = e
    least i h (fs j) lt = h j (pred-≤-pred lt)

firstFin : {n : ℕ} → (Fin n → Bool) → Mb.Maybe (Fin n)
firstFin p = Sum.rec (λ x → Mb.just (x .fst)) (λ _ → Mb.nothing) (find p)

-- The product state, as a tuple rather than a function.
--
-- `(i : Fin n) → Qs i` recomputes the `i`th component at every access,
-- so a scanner that inspects the state at each character re-walks that
-- component's whole transition chain each time -- quadratic in the
-- token, and the early exit of `GreedyMax` inspects at every character.
-- A nested pair is a constructor: each component is forced once and the
-- next state's is built on the forced one.
Tup : {m : ℕ} → (Fin m → Type ℓAlph) → Type ℓAlph
Tup {m = zero} Ps = Unit*
Tup {m = suc m} Ps = Ps fz × Tup (λ i → Ps (fs i))

_!_ : {m : ℕ} {Ps : Fin m → Type ℓAlph} → Tup Ps → (i : Fin m) → Ps i
_!_ {m = suc m} t fz = t .fst
_!_ {m = suc m} t (fs i) = t .snd ! i

tab : {m : ℕ} {Ps : Fin m → Type ℓAlph} → ((i : Fin m) → Ps i) → Tup Ps
tab {m = zero} f = tt*
tab {m = suc m} f = f fz , tab (λ i → f (fs i))

tab! : {m : ℕ} {Ps : Fin m → Type ℓAlph} (g : (i : Fin m) → Ps i)
  (i : Fin m) → (tab g ! i) Eq.≡ g i
tab! {m = suc m} g fz = Eq.refl
tab! {m = suc m} g (fs i) = tab! (λ j → g (fs j)) i

isSetTup : {m : ℕ} {Ps : Fin m → Type ℓAlph}
  → ((i : Fin m) → isSet (Ps i)) → isSet (Tup Ps)
isSetTup {m = zero} h = isSetUnit*
isSetTup {m = suc m} h = isSet× (h fz) (isSetTup (λ i → h (fs i)))

open DeterministicAutomaton

module Product {n : ℕ} (Qs : Fin n → Type ℓAlph)
  (M : (i : Fin n) → DeterministicAutomaton (Qs i))
  (Ds : (i : Fin n) → Deadness (M i))
  (sQ : (i : Fin n) → isSet (Qs i)) where

  -- `Fin n` is at level zero, so the tuple stays at `ℓAlph` -- which is
  -- what `Deterministic` demands of a state set.
  ProdQ : Type ℓAlph
  ProdQ = Tup Qs

  isSetProdQ : isSet ProdQ
  isSetProdQ = isSetTup sQ

  accAt : ProdQ → Fin n → Bool
  accAt f i = isAcc (M i) (f ! i)

  Prod : DeterministicAutomaton ProdQ
  Prod .init = tab λ i → init (M i)
  Prod .isAcc f = anyFin (accAt f)
  Prod .δ f c = tab λ i → δ (M i) (f ! i) c

  -- a product state is dead when every component is: a finite check over
  -- `Fin n`, and the two obligations are the components' own, pointwise
  deadAt : ProdQ → Fin n → Bool
  deadAt f i = Deadness.isDead (Ds i) (f ! i)

  ProdDead : Deadness Prod
  ProdDead .Deadness.isDead f = allFin (deadAt f)
  ProdDead .Deadness.dead-δ f c d = allFin-intro _ λ i →
    Eq.transport (λ q → Deadness.isDead (Ds i) q Eq.≡ true)
      (Eq.sym (tab! _ i))
      (Deadness.dead-δ (Ds i) (f ! i) c (allFin-elim (deadAt f) d i))
  ProdDead .Deadness.dead-rej f d =
    Eq.pathToEq (anyFin-false (accAt f) λ i →
      Eq.eqToPath (Deadness.dead-rej (Ds i) (f ! i)
        (allFin-elim (deadAt f) d i)))

  -- Priority readout at a product state.

  -- the priority answer at an arbitrary state, `Maybe` because an
  -- arbitrary state need not accept
  winner : ProdQ → Mb.Maybe (Fin n)
  winner f = firstFin (accAt f)

  -- Where it is known, the answer is the least accepting rule.
  -- This is `Found`'s left summand at `accAt f`, definitionally, so
  -- `find` produces it with nothing to rebuild.
  Wins : ProdQ → Type ℓ-zero
  Wins f = Σ[ i ∈ Fin n ]
      (accAt f i ≡ true)
      × ((j : Fin n) → toℕ j < toℕ i → accAt f j ≡ false)

  winner! : (f : ProdQ) → isAcc Prod f ≡ true → Wins f
  winner! f acc = winsFromFound (find (accAt f))
    where
    winsFromFound : Found (accAt f) → Wins f
    winsFromFound (Sum.inl x) = x
    winsFromFound (Sum.inr h) =
      Empty.rec (true≢false (sym acc ∙ anyFin-false _ h))

  scanProd = scan Prod isSetProdQ ProdDead

  runInit : ⊤Ty ⊢ Run Prod (init Prod)
  runInit = π (init Prod) ∘⊢ scanProd ∘⊢ readChars

  -- A token, as a grammar.
  --
  -- `GreedyMax`'s `Match q q'` carries `true Eq.≡ isAcc q'`, so the end
  -- state of a greedy match is *known* to accept, and `winner!` applies
  -- to it.  The winning rule is therefore a `⊕ᴰ` index computed from the
  -- state -- automaton data -- and not something read off a parse.
  --
  -- `Tok` spans the whole input: the `⊗` of `GreedyMax` splits it into
  -- the lexeme and the (refuted-as-extendable) remainder.

  Tok : TheoryTy _ tt
  Tok = ⊕[ q' ∈ ProdQ ] ⊕[ _ ∈ Wins q' ] GreedyMax Prod (init Prod) q'

  -- The readout, as a `⊢`-term.  `⊗⊕ᴰ-distL` pulls the acceptance
  -- equation out of the left factor, `winner!` turns it into the winning
  -- rule, and the match is put back exactly as it came.
  lexOne : Run Prod (init Prod)
    ⊢ Tok ⊕ ¬Ty (Trace Prod true (init Prod) ⊗ ⊤Ty)
  lexOne = ⊕-elim (inl ∘⊢ ⊕ᴰ-elim toTok) inr
    where
    -- `find` runs on the *state*, which is the `⊕ᴰ` tag the scan already
    -- produced; the match's own acceptance equation is reached only in
    -- the branch where the state rejects, which the equation refutes.
    -- Reaching for it in the live branch instead would force the `Match`
    -- pair at every one of the match's characters, and the readout would
    -- be quadratic.
    toTok : (q' : ProdQ) → GreedyMax Prod (init Prod) q' ⊢ Tok
    toTok q' = tokFromFound (find (accAt q'))
      where
      tokFromFound : Found (accAt q') → GreedyMax Prod (init Prod) q' ⊢ Tok
      tokFromFound (Sum.inl x) = σ⊕ q' ∘⊢ σ⊕ x
      tokFromFound (Sum.inr h) =
        ⊕ᴰ-elim (λ p → Empty.rec
          (true≢false (Eq.eqToPath p ∙ anyFin-false (accAt q') h)))
        ∘⊢ ⊗⊕ᴰ-distL
            {Y = true Eq.≡ isAcc Prod q'}
            {A = λ _ → TraceTo Prod (init Prod) q'}

  -- The display boundary.
  --
  -- `semact-text` recovers the characters under *any* grammar without
  -- looking at its parse: `⊤Ty-intro` forgets it, `readChars` reads the
  -- word back as a `char *`, and `semact-string` is the structural fold
  -- on that star.

  semact-text : {A : TheoryTy ℓA tt} → SemanticAction A String
  semact-text = semact-string ∘⊢ readChars ∘⊢ ⊤Ty-intro

  -- The winning rule, read at the display boundary.  `Wins q'` already
  -- names it, but projecting it out of the `⊕ᴰ` tag re-evaluates the
  -- state; `winner` recomputes it directly from the state instead, and
  -- the certificate serves the branch it rules out.
  winsIdx : (f : ProdQ) → Wins f → Fin n
  winsIdx f w = Mb.rec (w .fst) (λ i → i) (winner f)

  tokAction : SemanticAction Tok (Fin n × String × String)
  tokAction = semact-⊕ᴰ' λ q' → semact-⊕ᴰ' λ w →
    semact-map (λ p → winsIdx q' w , p) (semact-⊗₂ semact-text semact-text)

  lexAction : SemanticAction (Run Prod (init Prod))
    (Mb.Maybe (Fin n × String × String))
  lexAction =
    semact-⊕ (semact-map Mb.just tokAction) (semact-pure Mb.nothing)
    ∘⊢ lexOne

  -- the `Maybe` here is the external one
  lexOneS : String → Mb.Maybe (Fin n × String × String)
  lexOneS = observe runInit lexAction

  -- The tokenising loop.  DISPLAY LAYER, not a `⊢`-term: see the note
  -- at the bottom of this file.

  tokeniseFuel : ℕ → String → Mb.Maybe (List (Fin n × String))
  tokeniseFuel fuel [] = Mb.just []
  tokeniseFuel zero (c ∷ w) = Mb.nothing
  tokeniseFuel (suc fuel) (c ∷ w) = next (lexOneS (c ∷ w))
    where
    next : Mb.Maybe (Fin n × String × String)
      → Mb.Maybe (List (Fin n × String))
    next Mb.nothing = Mb.nothing
    next (Mb.just (i , [] , rest)) = Mb.nothing
    next (Mb.just (i , (d ∷ ds) , rest)) =
      Mb.map-Maybe ((i , d ∷ ds) ∷_) (tokeniseFuel fuel rest)

  tokenise : String → Mb.Maybe (List (Fin n × String))
  tokenise w = tokeniseFuel (length w) w
