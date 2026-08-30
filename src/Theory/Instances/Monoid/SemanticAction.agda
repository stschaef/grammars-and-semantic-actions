open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.SemanticAction
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

private variable ℓA ℓB ℓX ℓY : Level

open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma using (_×_ ; _,_)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
import Cubical.Data.Bool as Bool
open import Cubical.Data.FinData using (zero ; suc)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet hiding (Δ)
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet
open import Theory.Type.SemanticAction.Base MonEqns Alphabet (λ _ → tt) listPresentation public

-- The only parser-specific primitive action: expose the generator selected
-- by the monoid instance's `char` grammar.  All structural action laws live
-- in `Theory.Type.SemanticAction.Base`.
semact-char : SemanticAction char Alphabet
semact-char m (c , p) = c , tt

semact-⊗₁ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {X : Type ℓX}
  → SemanticAction A X → SemanticAction (A ⊗ B) X
semact-⊗₁ a m (ms , e , (p , _)) = a (ms zero) p

semact-⊗ᵣ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {X : Type ℓX}
  → SemanticAction B X → SemanticAction (A ⊗ B) X
semact-⊗ᵣ b m (ms , e , (_ , (q , _))) = b (ms (suc zero)) q

semact-⊗₂ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {X : Type ℓX} {Y : Type ℓY}
  → SemanticAction A X → SemanticAction B Y → SemanticAction (A ⊗ B) (X × Y)
semact-⊗₂ a b m (ms , e , (p , (q , _))) =
  (a (ms zero) p .fst , b (ms (suc zero)) q .fst) , tt

semact-* : {A : TheoryTy ℓA tt} {X : Type ℓX}
  → SemanticAction A X → SemanticAction (A *) (List X)
semact-* {A = A} {X = X} a = semact-rec alg tt
  where
  cons : (⟦ (⊗e _⊙_ (two (k A) (Var tt))) ⟧TheoryTy
            (λ _ → Δ (List X))) ⊢ Δ (List X)
  cons m (ms , e , xs) =
    (a (ms zero) ((xs zero) .lower) .fst ∷ ((xs (suc zero)) .lower) .fst) , tt

  alg : ∀ _ → ⟦ StarCode A ⟧TheoryTy (λ _ → Δ (List X)) ⊢ Δ (List X)
  alg _ = ⊕ᴰ-elim λ where
    Bool.false → semact-pure []
    Bool.true → cons

-- The same fold, dropping the steps that emit nothing, so a lexer never has
-- to filter a token list outside the theory.
semact-skip* : {A : TheoryTy ℓA tt} {X : Type ℓX}
  → SemanticAction A (Maybe X) → SemanticAction (A *) (List X)
semact-skip* {A = A} {X = X} a = semact-rec alg tt
  where
  push : Maybe X → List X → List X
  push nothing ys = ys
  push (just x) ys = x ∷ ys

  cons : (⟦ (⊗e _⊙_ (two (k A) (Var tt))) ⟧TheoryTy
            (λ _ → Δ (List X))) ⊢ Δ (List X)
  cons m (ms , e , xs) =
    push (a (ms zero) ((xs zero) .lower) .fst)
         (((xs (suc zero)) .lower) .fst) , tt

  alg : ∀ _ → ⟦ StarCode A ⟧TheoryTy (λ _ → Δ (List X)) ⊢ Δ (List X)
  alg _ = ⊕ᴰ-elim λ where
    Bool.false → semact-pure []
    Bool.true → cons

-- A structural scanner over canonical strings.  The classifier may emit one
-- token, skip its input character, or fail; this is independent of Unicode.
scanAction : {Token : Type ℓX}
  → (Alphabet → Maybe (Maybe Token))
  → SemanticAction String* (Maybe (List Token))
scanAction {Token = Token} classify = semact-rec alg tt
  where
  step : Alphabet → Maybe (List Token) → Maybe (List Token)
  step c rest with classify c
  ... | nothing = nothing
  ... | just nothing = rest
  ... | just (just t) with rest
  ... | nothing = nothing
  ... | just ts = just (t ∷ ts)

  cons : (⟦ (⊗e _⊙_ (two (k char) (Var tt))) ⟧TheoryTy
            (λ _ → Δ (Maybe (List Token)))) ⊢ Δ (Maybe (List Token))
  cons m (ms , e , xs) =
    step (semact-char (ms zero) ((xs zero) .lower) .fst)
         ((xs (suc zero)) .lower .fst)
    , tt

  alg : ∀ _ → ⟦ KleeneCode ⟧TheoryTy (λ _ → Δ (Maybe (List Token)))
    ⊢ Δ (Maybe (List Token))
  alg _ = ⊕ᴰ-elim λ where
    Bool.false → semact-pure (just [])
    Bool.true → cons

semact-string : SemanticAction (char *) (List Alphabet)
semact-string = semact-* semact-char

-- `String*` is the canonical right-nested list presentation used by the
-- parser library.  It is deliberately not identified definitionally with
-- the generic Kleene star, so it receives its own structural observation.
semact-String* : SemanticAction String* (List Alphabet)
semact-String* = semact-rec alg tt
  where
  cons : (⟦ (⊗e _⊙_ (two (k char) (Var tt))) ⟧TheoryTy
            (λ _ → Δ (List Alphabet))) ⊢ Δ (List Alphabet)
  cons m (ms , e , xs) =
    (semact-char (ms zero) ((xs zero) .lower) .fst
      ∷ ((xs (suc zero)) .lower) .fst) , tt

  alg : ∀ _ → ⟦ KleeneCode ⟧TheoryTy (λ _ → Δ (List Alphabet)) ⊢ Δ (List Alphabet)
  alg _ = ⊕ᴰ-elim λ where
    Bool.false → semact-pure []
    Bool.true → cons
