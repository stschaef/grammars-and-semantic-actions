{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Maximal munch in one pass.

   `Run q` is the answer for a run started in state `q`: either a greedy
   match, tagged with the state it ended in, or a refutation that any
   prefix at all matches.  `Table` holds a `Run` for *every* state, and
   the scan is a fold over the input producing one.

   That table is the whole performance argument.  The recursive call is
   made once per character and consulted at `δ q c` for each `q`, so a
   run over `n` characters costs `n · |Q|` rather than one pass per
   candidate match -- which is what made the two-lookup tokenisation loop
   blow up when the residual set was not shared.

   The greedy witness is `GreedyAt`, whose residual index is the language
   of the state the match *ends* in.  That index is exactly the `⊕[ q' ]`
   tag, and it is why extending a match is O(1): `extendAt` leaves the
   residual alone, because prepending a character does not move the end
   of the match. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Automaton.Scan
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using ([] ; _∷_ ; _++_)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.Unit using (tt ; tt*)
import Cubical.Data.Equality as Eq
import Cubical.Data.Empty as Empty
import Cubical.Data.List.Properties as L

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar.Guarded Alphabet isSetAlphabet
  using (¬Nullable ; ⊗-¬Nullable ; char-¬Nullable ; fold*g)
open import Theory.Instances.Monoid.Greedy.Base Alphabet isSetAlphabet
  using (GreedyAt ; extendAt ; char⁺ ; noExt-step)
open import Theory.Instances.Monoid.Derivative Alphabet isSetAlphabet using (Dl)
open import Theory.Instances.Monoid.Precise Alphabet isSetAlphabet using (flat)
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet using (_⊸_)
open import Theory.Instances.Monoid.Automaton.Base Alphabet isSetAlphabet
open import Theory.Type.Decidable.Base MonEqns Alphabet (λ _ → tt)
  listPresentation
open import Theory.Type.HLevels MonEqns Alphabet (λ _ → tt) listPresentation

private variable ℓA ℓB ℓQ ℓL : Level

-- `¬Nullable` transfers backwards along any map, which is all that is
-- needed to see `A & char⁺` cannot be empty.
&-¬NullableR : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → ¬Nullable B → ¬Nullable (A & B)
&-¬NullableR nu = nu ∘⊢ (π₂ ,&p id⊢)

char⁺-¬Nullable : ¬Nullable char⁺
char⁺-¬Nullable = ⊗-¬Nullable char-¬Nullable

-- ...and a non-nullable grammar is refuted at ε
¬Nullable→¬ε : {A : TheoryTy ℓA tt} → ¬Nullable A → εTy ⊢ ¬Ty A
¬Nullable→¬ε nu = ⇒-intro (nu ∘⊢ &-swap)

module _ {ℓQ ℓL} (M : DerivAutomaton ℓQ ℓL) where
  open DerivAutomaton M

  -- the answer for a run from `q`: a greedy match tagged with its end
  -- state, or a refutation of every match
  Run : Q → TheoryTy _ tt
  Run q = (⊕[ q' ∈ Q ] GreedyAt (L q) (L q')) ⊕ ¬Ty (L q ⊗ ⊤Ty)

  Table : TheoryTy _ tt
  Table = &[ q ∈ Q ] Run q

  ------------------------------------------------------------------
  -- ε: a state answers with the empty match exactly when it accepts.

  private
    -- nothing nonempty extends anything, when there is no input left
    noExt-ε : (R : TheoryTy ℓL tt) → εTy ⊢ ¬Ty ((R & char⁺) ⊗ ⊤Ty)
    noExt-ε R = ¬Nullable→¬ε (⊗-¬Nullable (&-¬NullableR char⁺-¬Nullable))

  scan-nil : εTy ⊢ Table
  scan-nil = &ᴰ-intro λ q → go q (acc q) Eq.refl
    where
    go : (q : Q) (b : Bool) → acc q Eq.≡ b → εTy ⊢ Run q
    go q true p =
      inl ∘⊢ σ⊕ q ∘⊢ (accY q p ,⊗ noExt-ε (L q)) ∘⊢ ⊗-unit-l⁻ε
      where
      ⊗-unit-l⁻ε : εTy ⊢ εTy ⊗ εTy
      ⊗-unit-l⁻ε m e = two [] [] , e .snd .fst , (εTy-pt , (εTy-pt , tt*))
    go q false p = inr ∘⊢ ¬Nullable→¬ε (⊗-¬Nullable (accN q p))

  ------------------------------------------------------------------
  -- c ∷ w: consult the recursive answer at `δ q c`.

  private
    -- functoriality of the match half; the residual index is untouched
    GreedyAt-map : {A : TheoryTy ℓA tt} {A' : TheoryTy ℓB tt}
      {R : TheoryTy ℓL tt} → A ⊢ A' → GreedyAt A R ⊢ GreedyAt A' R
    GreedyAt-map f = f ,⊗ id⊢

  scan-cons : char ⊗ Table ⊢ Table
  scan-cons = &ᴰ-intro λ q → ⊕ᴰ-elim (λ c → stepAt q c) ∘⊢ charSplit
    where
    charSplit : char ⊗ Table ⊢ ⊕[ c ∈ Alphabet ] (literal c ⊗ Table)
    charSplit m (ms , e , ((c , lc) , (t , _))) =
      c , ms , e , (lc , (t , tt*))

    stepAt : (q : Q) (c : Alphabet) → literal c ⊗ Table ⊢ Run q
    stepAt q c = ⊕-elim matched unmatched ∘⊢ ⊗⊕-distR ∘⊢ (id⊢ ,⊗ π (δ q c))
      where
      -- the recursive run matched: prepend the character, O(1)
      matched : literal c ⊗ (⊕[ q' ∈ Q ] GreedyAt (L (δ q c)) (L q')) ⊢ Run q
      matched = inl ∘⊢ ⊕ᴰ-elim (λ q' → σ⊕ q' ∘⊢ ext q') ∘⊢ pushΣ
        where
        pushΣ : literal c ⊗ (⊕[ q' ∈ Q ] GreedyAt (L (δ q c)) (L q'))
                 ⊢ ⊕[ q' ∈ Q ] (literal c ⊗ GreedyAt (L (δ q c)) (L q'))
        pushΣ m (ms , e , (lc , ((q' , g) , _))) =
          q' , ms , e , (lc , (g , tt*))

        ext : (q' : Q) → literal c ⊗ GreedyAt (L (δ q c)) (L q')
                       ⊢ GreedyAt (L q) (L q')
        ext q' = extendAt c ∘⊢ (id⊢ ,⊗ GreedyAt-map (δ-Dl⁻ q c))

      -- the recursive run did not: either `q` accepts ε and the empty
      -- match is greedy, or nothing matches from `q` either
      unmatched : literal c ⊗ ¬Ty (L (δ q c) ⊗ ⊤Ty) ⊢ Run q
      unmatched = go (acc q) Eq.refl
        where
        -- the refutation the greedy witness wants: nothing nonempty
        -- continues, because a nonempty prefix starts with `c` and its
        -- tail would be an `L (δ q c)`
        noMore : literal c ⊗ ¬Ty (L (δ q c) ⊗ ⊤Ty) ⊢ ¬Ty ((L q & char⁺) ⊗ ⊤Ty)
        noMore = noExt-step c ∘⊢ (id⊢ ,⊗ ¬Ty-map (δ-⊸⁻ q c ,⊗ id⊢))

        go : (b : Bool) → acc q Eq.≡ b
           → literal c ⊗ ¬Ty (L (δ q c) ⊗ ⊤Ty) ⊢ Run q
        go true p = inl ∘⊢ σ⊕ q ∘⊢ (accY q p ,⊗ id⊢) ∘⊢ ε⊗-intro ∘⊢ noMore
          where
          ε⊗-intro : {X : TheoryTy ℓA tt} → X ⊢ εTy ⊗ X
          ε⊗-intro m x = two [] m , Eq.refl , (εTy-pt , (x , tt*))
        -- ...or `q` rejects ε too, and then nothing matches at all: a
        -- match is either empty, which `accN` refutes, or starts with
        -- `c`, whose tail the recursive refutation refutes.
        go false p = inr ∘⊢ noneAt
          where
          noneAt : literal c ⊗ ¬Ty (L (δ q c) ⊗ ⊤Ty) ⊢ ¬Ty (L q ⊗ ⊤Ty)
          noneAt m (ms , e , (lc , (nk , _))) t =
            go' (ns zero) (t .snd .snd .fst)
              (Eq.eqToPath (t .snd .fst) ∙ sym whole)
            where
            ns = t .fst
            ns1 = ns (suc zero)
            ms1 = ms (suc zero)

            whole : c ∷ ms1 ≡ m
            whole = flat c (ms zero) ms1 m lc e

            go' : (u : String) → L q u → u ++ ns1 ≡ c ∷ ms1 → ⊥Ty m
            go' [] a q≡ = Empty.rec (accN q p [] (a , εTy-pt) .lower)
            go' (d ∷ u) a q≡ =
              Empty.rec (nk (two u ns1 , Eq.pathToEq (L.cons-inj₂ q≡)
                , (δ-Dl q c u (subst (L q) headed a) , (tt , tt*))) .lower)
              where
              headed : d ∷ u ≡ c ∷ u
              headed = cong (_∷ u) (L.cons-inj₁ q≡)

  ------------------------------------------------------------------
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
        isSet⊗bin (isSetL q) λ m → isProp→isSet (isProp¬Ty _))
      (λ m → isProp→isSet (isProp¬Ty _))

  scan : char * ⊢ Table
  scan = fold*g (Table , isSetTable) char-¬Nullable scan-nil scan-cons
