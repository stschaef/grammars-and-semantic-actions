{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Maximal munch over a deterministic automaton.  `GreedyAt` indexes by the
   residual, so extending is O(1); `Table` makes one recursive call per character. -}
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
  using (⊗⊕ᴰ-distL ; ⊗⊕ᴰ-distR)
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

module States {Q : Type ℓAlph} (M : DeterministicAutomaton Q) where
  open DeterministicAutomaton M

  L : Q → TheoryTy _ tt
  L q = Trace true q

  accY : (q : Q) → isAcc q Eq.≡ true → εTy ⊢ L q
  accY q p = Eq.transport (λ b → εTy ⊢ Trace b q) p (STOP q ∘⊢ liftTy)

  accN : (q : Q) → isAcc q Eq.≡ false → ¬Nullable (L q)
  accN q p = ¬Nullable-map (unrollTrace true q)
    (⊕-¬Nullable
      (⊕ᴰ-¬Nullable λ c → ⊗-¬Nullable (literal-¬Nullable c))
      (⊕ᴰ-¬Nullable λ pp → Empty.rec (true≢false (Eq.eqToPath (pp Eq.∙ p)))))

noExt-ε : (R : TheoryTy ℓL tt) → εTy ⊢ ¬Ty ((R & char⁺) ⊗ ⊤Ty)
noExt-ε R = ¬Nullable→¬ε (⊗-¬Nullable (&-¬NullableR char⁺-¬Nullable))

module _ {Q : Type ℓAlph} (M : DeterministicAutomaton Q) (isSetQ : isSet Q) where
  open DeterministicAutomaton M
  open States M

  private
    δ-Dl⁻ : (q : Q) (c : Alphabet) → L (δ q c) ⊢ Dl c (L q)
    δ-Dl⁻ q c = Trace→Dl true q c

    δ-⊸⁻ : (q : Q) (c : Alphabet) → literal c ⊸ L q ⊢ L (δ q c)
    δ-⊸⁻ q c = ∂→Trace true q c ∘⊢ ⊸→∂⌈⌉ (⌈gen c ⌉) {B = L q}

  Run : Q → TheoryTy _ tt
  Run q = (⊕[ q' ∈ Q ] GreedyAt (L q) (L q')) ⊕ ¬Ty (L q ⊗ ⊤Ty)

  Table : TheoryTy _ tt
  Table = &[ q ∈ Q ] Run q

  scan-nil : εTy ⊢ Table
  scan-nil = &ᴰ-intro λ q → go q (isAcc q) Eq.refl
    where
    go : (q : Q) (b : Bool) → isAcc q Eq.≡ b → εTy ⊢ Run q
    go q true p =
      inl ∘⊢ σ⊕ q ∘⊢ (accY q p ,⊗ noExt-ε (L q)) ∘⊢ ε⊗-intro
    go q false p = inr ∘⊢ ¬Nullable→¬ε (⊗-¬Nullable (accN q p))

  private
    GreedyAt-map : {A : TheoryTy ℓA tt} {A' : TheoryTy ℓB tt}
      {R : TheoryTy ℓL tt} → A ⊢ A' → GreedyAt A R ⊢ GreedyAt A' R
    GreedyAt-map f = f ,⊗ id⊢

  scan-cons : char ⊗ Table ⊢ Table
  scan-cons = &ᴰ-intro λ q → ⊕ᴰ-elim (λ c → stepAt q c) ∘⊢ ⊗⊕ᴰ-distL
    where
    stepAt : (q : Q) (c : Alphabet) → literal c ⊗ Table ⊢ Run q
    stepAt q c = ⊕-elim matched unmatched ∘⊢ ⊗⊕-distR ∘⊢ (id⊢ ,⊗ π (δ q c))
      where
      matched : literal c ⊗ (⊕[ q' ∈ Q ] GreedyAt (L (δ q c)) (L q')) ⊢ Run q
      matched = inl ∘⊢ ⊕ᴰ-elim (λ q' → σ⊕ q' ∘⊢ ext q') ∘⊢ ⊗⊕ᴰ-distR
        where
        ext : (q' : Q) → literal c ⊗ GreedyAt (L (δ q c)) (L q')
                       ⊢ GreedyAt (L q) (L q')
        ext q' = extendAt c ∘⊢ (id⊢ ,⊗ GreedyAt-map (δ-Dl⁻ q c))

      unmatched : literal c ⊗ ¬Ty (L (δ q c) ⊗ ⊤Ty) ⊢ Run q
      unmatched = go (isAcc q) Eq.refl
        where
        -- a nonempty continuation starts with `c` and its tail is an `L (δ q c)`
        noMore : literal c ⊗ ¬Ty (L (δ q c) ⊗ ⊤Ty) ⊢ ¬Ty ((L q & char⁺) ⊗ ⊤Ty)
        noMore = noExt-step c ∘⊢ (id⊢ ,⊗ ¬Ty-map (δ-⊸⁻ q c ,⊗ id⊢))

        go : (b : Bool) → isAcc q Eq.≡ b
           → literal c ⊗ ¬Ty (L (δ q c) ⊗ ⊤Ty) ⊢ Run q
        go true p = inl ∘⊢ σ⊕ q ∘⊢ (accY q p ,⊗ id⊢) ∘⊢ ε⊗-intro ∘⊢ noMore
        -- rejecting ε means every match is a `char⁺`, already refuted by `noMore`
        go false p =
          inr ∘⊢ ¬Ty-map ((id⊢ ,& ¬Nullable→char⁺ (accN q p)) ,⊗ id⊢) ∘⊢ noMore

  -- `char` is non-nullable, so Löb closes the fold: one pass, no TERMINATING.

  private
    isSetTable : isSetTheoryTy Table
    isSetTable = isSet&ᴰ λ q → isSet⊕
      (isSet⊕ᴰ isSetQ λ q' →
        isSet⊗2 (isSetTrace true q)
          λ m → isProp→isSet (isProp¬Ty ((L q' & char⁺) ⊗ ⊤Ty)))
      (λ m → isProp→isSet (isProp¬Ty (L q ⊗ ⊤Ty)))

  scan : char * ⊢ Table
  scan = fold*g (Table , isSetTable) char-¬Nullable scan-nil scan-cons
