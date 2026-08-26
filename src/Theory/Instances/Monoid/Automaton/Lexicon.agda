{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A lexicon: several token rules, longest match across all of them,
   ties broken by rule priority.

   A lexicon is *not* `⊕Aut` of its rules.  That construction wants the
   rules' first sets disjoint, and a lexicon deliberately overlaps --
   `where` is also an identifier -- and resolves the overlap by priority.

   So run every rule at once instead: the state is a tuple of the rules'
   states, `δ` steps each component, and the product accepts when *some*
   rule does.  `Fin n → Qs i` keeps that at `ℓAlph`, so `Deterministic`'s
   `parse` and `Greedy`'s `scan` apply unchanged, and maximal munch over
   the product is longest match across the whole lexicon.

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

open import Cubical.Data.Bool using (Bool ; true ; false ; _or_ ; true≢false)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order using (_<_ ; ¬-<-zero ; pred-≤-pred)
open import Cubical.Data.FinData using (Fin ; toℕ) renaming (zero to fz ; suc to fs)
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Maybe as Mb
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet
  using (readChars)
open import Theory.Instances.Monoid.Automaton.Deterministic
  Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Greedy Alphabet isSetAlphabet
  using (scan)

------------------------------------------------------------------------
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

-- The readout, with its evidence: the least `true`, or a refutation of
-- every index.  Priority *is* this minimality.
Found : {n : ℕ} → (Fin n → Bool) → Type ℓ-zero
Found {n = n} p =
  (Σ[ i ∈ Fin n ] (p i ≡ true)
     × ((j : Fin n) → toℕ j < toℕ i → p j ≡ false))
  Sum.⊎ ((i : Fin n) → p i ≡ false)

find : {n : ℕ} (p : Fin n → Bool) → Found p
find {n = zero} p = Sum.inr λ ()
find {n = suc n} p = go (p fz) refl
  where
  go : (b : Bool) → p fz ≡ b → Found p
  go true e = Sum.inl (fz , e , λ j lt → Empty.rec (¬-<-zero lt))
  go false e = Sum.rec
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

------------------------------------------------------------------------
-- The product automaton.

open DeterministicAutomaton

module Product {n : ℕ} (Qs : Fin n → Type ℓAlph)
  (M : (i : Fin n) → DeterministicAutomaton (Qs i))
  (sQ : (i : Fin n) → isSet (Qs i)) where

  -- `Fin n` is at level zero, so the tuple stays at `ℓAlph` -- which is
  -- what `Deterministic` demands of a state set.
  ProdQ : Type ℓAlph
  ProdQ = (i : Fin n) → Qs i

  isSetProdQ : isSet ProdQ
  isSetProdQ = isSetΠ sQ

  -- the acceptance profile of a product state: which rules accept here
  accAt : ProdQ → Fin n → Bool
  accAt f i = isAcc (M i) (f i)

  Prod : DeterministicAutomaton ProdQ
  Prod .init i = init (M i)
  Prod .isAcc f = anyFin (accAt f)
  Prod .δ f c i = δ (M i) (f i) c

  ------------------------------------------------------------------
  -- Priority readout at a product state.

  -- `Maybe`, not a total function: `Greedy`'s `Run q` names the end
  -- state of the match but does not record in its type that the state
  -- accepts, so the readout cannot assume it.
  winner : ProdQ → Mb.Maybe (Fin n)
  winner f = firstFin (accAt f)

  -- ...and where it is known, the answer is the least accepting rule.
  Wins : ProdQ → Type ℓ-zero
  Wins f = Σ[ i ∈ Fin n ]
      (accAt f i ≡ true)
      × ((j : Fin n) → toℕ j < toℕ i → accAt f j ≡ false)
      × (winner f ≡ Mb.just i)

  winner! : (f : ProdQ) → isAcc Prod f ≡ true → Wins f
  winner! f acc = go (find (accAt f)) refl
    where
    go : (s : Found (accAt f)) → find (accAt f) ≡ s → Wins f
    go (Sum.inl x) e = x .fst , x .snd .fst , x .snd .snd ,
      cong (Sum.rec (λ y → Mb.just (y .fst)) (λ _ → Mb.nothing)) e
    go (Sum.inr h) e = Empty.rec (true≢false (sym acc ∙ anyFin-false _ h))

  ------------------------------------------------------------------
  -- Maximal munch over the product = longest match across the lexicon.

  scanProd = scan Prod isSetProdQ

  -- The greedy match from the initial product state: the winning rule,
  -- the token, and what is left.  `scan`'s witness already names the end
  -- state, so the rule is read off it with no second pass.
  lexOne : String → Mb.Maybe (Fin n × String × String)
  lexOne w = Sum.rec
    (λ x → Mb.map-Maybe (λ i → i , x .snd .fst fz , x .snd .fst (fs fz))
                  (winner (x .fst)))
    (λ _ → Mb.nothing)
    (scanProd w (readChars w tt) (init Prod))

  ------------------------------------------------------------------
  -- The tokenising loop.
  --
  -- QUADRATIC, and not honestly fixable from here: `scan` is a fold over
  -- the *whole* remaining input, so restarting it at each token boundary
  -- costs O(n) per token, O(n·k) overall.  A linear tokeniser would have
  -- to keep the fold's intermediate tables -- `scan` computes a `Table`
  -- at every suffix already -- and read the next token out of the table
  -- at the previous token's end, which `Greedy` does not expose.
  --
  -- Fuel, not `TERMINATING`: an empty match would not shrink the input,
  -- so it is refused rather than looped on.

  tokeniseFuel : ℕ → String → Mb.Maybe (List (Fin n × String))
  tokeniseFuel fuel [] = Mb.just []
  tokeniseFuel zero (c ∷ w) = Mb.nothing
  tokeniseFuel (suc fuel) (c ∷ w) = next (lexOne (c ∷ w))
    where
    next : Mb.Maybe (Fin n × String × String)
      → Mb.Maybe (List (Fin n × String))
    next Mb.nothing = Mb.nothing
    next (Mb.just (i , [] , rest)) = Mb.nothing
    next (Mb.just (i , (d ∷ ds) , rest)) =
      Mb.map-Maybe ((i , d ∷ ds) ∷_) (tokeniseFuel fuel rest)

  tokenise : String → Mb.Maybe (List (Fin n × String))
  tokenise w = tokeniseFuel (length w) w
