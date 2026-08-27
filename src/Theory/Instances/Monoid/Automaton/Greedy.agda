{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Maximal munch over a deterministic automaton.

   `GreedyAt` indexes by the residual rather than the matched word, and
   over an automaton the residual after a match is the state it ended in
   -- the `⊕[ q' ]` tag the recursive call already produces.  Extending is
   then an associativity and a substitution, not the O(n²) rebuild of
   `Grammar/Greedy/Automata`.  `Table` holds a `Run` per state, so the
   recursive call is made once per character.  Nothing is assumed of the
   automaton: that `δ` computes the derivative and that a state rejecting
   ε has no empty run are theorems of `Deterministic`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Automaton.Greedy
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool ; true≢false)
open import Cubical.Data.List using ([] ; _∷_ ; _++_)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.Unit using (tt ; tt*)
import Cubical.Data.Equality as Eq
import Cubical.Data.Empty as Empty

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar.Guarded Alphabet isSetAlphabet
  using (¬Nullable ; ⊗-¬Nullable ; ⊕-¬Nullable ; char-¬Nullable
       ; literal-¬Nullable ; fold*g)
open import Theory.Instances.Monoid.Greedy.Base Alphabet isSetAlphabet
  using (GreedyAt ; extendAt ; char⁺ ; noExt-step)
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⊗⊕ᴰ-distL ; ⊗⊕ᴰ-distR ; &⊕ᴰ-distL)
open import Theory.Instances.Monoid.Derivative Alphabet isSetAlphabet using (Dl)
open import Theory.Instances.Monoid.Derivative.General Alphabet isSetAlphabet
  using (⊸→∂⌈⌉)
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet using (_⊸_)
open import Theory.Instances.Monoid.Automaton.Deterministic
  Alphabet isSetAlphabet
open import Theory.Instances.Monoid.SequentialUnambiguity.Nullable
  Alphabet isSetAlphabet
  using (¬Nullable-map ; &-¬NullableR ; ⊕ᴰ-¬Nullable ; char⁺-¬Nullable
        ; ¬Nullable→¬ε ; ¬Nullable→char⁺) public
open import Theory.Type.Decidable.Base MonEqns Alphabet (λ _ → tt)
  listPresentation
open import Theory.Type.HLevels MonEqns Alphabet (λ _ → tt) listPresentation

private variable ℓA ℓB ℓL ℓY : Level

module _ {Q : Type ℓAlph} (M : DeterministicAutomaton Q) (isSetQ : isSet Q) where
  open DeterministicAutomaton M

  -- the language of a state is its accepting runs
  private
    L : Q → TheoryTy _ tt
    L q = Trace true q

    -- ε is accepted exactly by an accepting state.  A step needs a
    -- letter, and the stop branch carries `true ≡ isAcc q`.
    accY : (q : Q) → isAcc q Eq.≡ true → εTy ⊢ L q
    accY q p = Eq.transport (λ b → εTy ⊢ Trace b q) p (STOP q ∘⊢ liftTy)

    accN : (q : Q) → isAcc q Eq.≡ false → ¬Nullable (L q)
    accN q p = ¬Nullable-map (unrollTrace true q)
      (⊕-¬Nullable
        (⊕ᴰ-¬Nullable λ c → ⊗-¬Nullable (literal-¬Nullable c))
        -- the stop branch carries `true ≡ isAcc q`, and `q` rejects ε
        (⊕ᴰ-¬Nullable λ pp → Empty.rec (true≢false (Eq.eqToPath (pp Eq.∙ p)))))

    -- `δ` computes the derivative: both directions are theorems there
    δ-Dl⁻ : (q : Q) (c : Alphabet) → L (δ q c) ⊢ Dl c (L q)
    δ-Dl⁻ q c = Trace→Dl true q c

    δ-⊸⁻ : (q : Q) (c : Alphabet) → literal c ⊸ L q ⊢ L (δ q c)
    δ-⊸⁻ q c = ∂→Trace true q c ∘⊢ ⊸→∂⌈⌉ (⌈gen c ⌉) {B = L q}

  -- the answer for a run from `q`: a greedy match tagged with its end
  -- state, or a refutation of every match
  Run : Q → TheoryTy _ tt
  Run q = (⊕[ q' ∈ Q ] GreedyAt (L q) (L q')) ⊕ ¬Ty (L q ⊗ ⊤Ty)

  Table : TheoryTy _ tt
  Table = &[ q ∈ Q ] Run q

  -- ε: a state answers with the empty match exactly when it accepts.

  private
    -- nothing nonempty extends anything, when there is no input left
    noExt-ε : (R : TheoryTy ℓL tt) → εTy ⊢ ¬Ty ((R & char⁺) ⊗ ⊤Ty)
    noExt-ε R = ¬Nullable→¬ε (⊗-¬Nullable (&-¬NullableR char⁺-¬Nullable))

  scan-nil : εTy ⊢ Table
  scan-nil = &ᴰ-intro λ q → go q (isAcc q) Eq.refl
    where
    go : (q : Q) (b : Bool) → isAcc q Eq.≡ b → εTy ⊢ Run q
    go q true p =
      inl ∘⊢ σ⊕ q ∘⊢ (accY q p ,⊗ noExt-ε (L q)) ∘⊢ ε⊗-intro
    go q false p = inr ∘⊢ ¬Nullable→¬ε (⊗-¬Nullable (accN q p))

  -- c ∷ w: consult the recursive answer at `δ q c`.

  private
    -- functoriality of the match half; the residual index is untouched
    GreedyAt-map : {A : TheoryTy ℓA tt} {A' : TheoryTy ℓB tt}
      {R : TheoryTy ℓL tt} → A ⊢ A' → GreedyAt A R ⊢ GreedyAt A' R
    GreedyAt-map f = f ,⊗ id⊢

  scan-cons : char ⊗ Table ⊢ Table
  scan-cons = &ᴰ-intro λ q → ⊕ᴰ-elim (λ c → stepAt q c) ∘⊢ ⊗⊕ᴰ-distL
    where
    stepAt : (q : Q) (c : Alphabet) → literal c ⊗ Table ⊢ Run q
    stepAt q c = ⊕-elim matched unmatched ∘⊢ ⊗⊕-distR ∘⊢ (id⊢ ,⊗ π (δ q c))
      where
      -- the recursive run matched: prepend the character, O(1)
      matched : literal c ⊗ (⊕[ q' ∈ Q ] GreedyAt (L (δ q c)) (L q')) ⊢ Run q
      matched = inl ∘⊢ ⊕ᴰ-elim (λ q' → σ⊕ q' ∘⊢ ext q') ∘⊢ ⊗⊕ᴰ-distR
        where
        ext : (q' : Q) → literal c ⊗ GreedyAt (L (δ q c)) (L q')
                       ⊢ GreedyAt (L q) (L q')
        ext q' = extendAt c ∘⊢ (id⊢ ,⊗ GreedyAt-map (δ-Dl⁻ q c))

      -- the recursive run did not: either `q` accepts ε and the empty
      -- match is greedy, or nothing matches from `q` either
      unmatched : literal c ⊗ ¬Ty (L (δ q c) ⊗ ⊤Ty) ⊢ Run q
      unmatched = go (isAcc q) Eq.refl
        where
        -- the refutation the greedy witness wants: nothing nonempty
        -- continues, because a nonempty prefix starts with `c` and its
        -- tail would be an `L (δ q c)`
        noMore : literal c ⊗ ¬Ty (L (δ q c) ⊗ ⊤Ty) ⊢ ¬Ty ((L q & char⁺) ⊗ ⊤Ty)
        noMore = noExt-step c ∘⊢ (id⊢ ,⊗ ¬Ty-map (δ-⊸⁻ q c ,⊗ id⊢))

        go : (b : Bool) → isAcc q Eq.≡ b
           → literal c ⊗ ¬Ty (L (δ q c) ⊗ ⊤Ty) ⊢ Run q
        go true p = inl ∘⊢ σ⊕ q ∘⊢ (accY q p ,⊗ id⊢) ∘⊢ ε⊗-intro ∘⊢ noMore
        -- ...or `q` rejects ε too, and then nothing matches at all.
        -- Rejecting ε means every match is a `char⁺`, and `noMore` has
        -- already refuted those.
        go false p =
          inr ∘⊢ ¬Ty-map ((id⊢ ,& ¬Nullable→char⁺ (accN q p)) ,⊗ id⊢) ∘⊢ noMore

  -- ...and the fold.  `char` is non-nullable, so Löb closes it: one
  -- pass, no `TERMINATING`.

  private
    isSet⊗bin : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
      → isSetTheoryTy A → isSetTheoryTy B → isSetTheoryTy (A ⊗ B)
    isSet⊗bin sA sB = isSet⊗ _⊙_ _ _ λ where
      zero → sA
      (suc zero) → sB

    isSetTable : isSetTheoryTy Table
    isSetTable = isSet&ᴰ λ q → isSet⊕
      (isSet⊕ᴰ isSetQ λ q' →
        isSet⊗bin (isSetTrace true q) λ m → isProp→isSet (isProp¬Ty _))
      (λ m → isProp→isSet (isProp¬Ty _))

  scan : char * ⊢ Table
  scan = fold*g (Table , isSetTable) char-¬Nullable scan-nil scan-cons
