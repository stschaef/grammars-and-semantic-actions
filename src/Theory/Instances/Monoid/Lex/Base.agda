{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
-- A lexer is `many` over a one-token parser.  Rule priority is `<|>`'s bias
-- and skipping is the action's `nothing`; neither needs new machinery.
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Lex.Base
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Cubical.Data.List using (List ; [] ; _∷_)
import Cubical.Data.Maybe as M
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Combinator.Incomplete.Star Alphabet _≟_ ℓ
  public
open import Theory.Instances.Monoid.KleeneStar.Guarded Alphabet isSetAlphabet
  public

private variable ℓA ℓTok : Level

-- `nothing` skips the matched text, `just t` emits a token.
Emit : {T : Type ℓTok} {A : TheoryTy ℓA tt} → Type _
Emit {T = T} {A = A} = SemanticAction A (M.Maybe T)

module _ {T : Type ℓTok} (Tk : TheorySet ℓA tt) where
  -- the token stream grammar: a repetition of whatever one token is
  Tokens : TheorySet (ℓF ℓA) tt
  Tokens = StarSet Tk

  module _ (p : ⊤Ty ⊢ Parser (ℓ⊗ (ℓF ℓA) (ℓ-max ℓM ℓ)) ⟨▷⟩ ⟨□⟩ Tk) where
    lexP : ⊤Ty ⊢ Parser (ℓ-max ℓM ℓ) ⟨□⟩ ⟨□⟩ Tokens
    lexP = many ℓ Tk p

    lexTest : Test (ty Tokens)
    lexTest = runP ℓ lexP

    -- the sole boundary at which a token list leaves the theory.  The fold
    -- is `semact-skip*g`, i.e. löb -- not `semact-skip*`, which is `rec`
    -- and carries the pragma.  The price is the token grammar's
    -- non-nullability, which is what stops a lexer looping on ε anyway.
    lex : isSet T → ¬Nullable (ty Tk) → (act : Emit {T = T} {A = ty Tk})
        → String → M.Maybe (List T)
    lex isSetT nu act =
      observe lexTest (semact-Maybe (semact-skip*g isSetT nu act))
