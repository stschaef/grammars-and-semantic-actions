{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.Examples
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Unit using (Unit ; tt)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet

private variable ℓA : Level

-- A non-nullable test grammar.  Its only successful layer removes one `a`
-- before making the recursive star call.
LiteralStar : Alphabet → TheoryTy (ℓF ℓM) tt
LiteralStar a = (literal a) *

literalStar-NIL : {a : Alphabet} → LiftTheoryTy (ℓF ℓM) εTy ⊢ LiteralStar a
literalStar-NIL = NIL

literalStar-CONS : {a : Alphabet}
  → literal a ⊗ LiteralStar a ⊢ LiteralStar a
literalStar-CONS = CONS

dyckBranch : (lp rp : Alphabet) → Bool
  → Functor ℓM Unit (λ _ → tt) tt
dyckBranch lp rp false = k εTy
dyckBranch lp rp true =
  ⊗e _⊙_ (two (k (literal lp))
    (⊗e _⊙_ (two (Var tt)
      (⊗e _⊙_ (two (k (literal rp)) (Var tt))))))

DyckCode : (lp rp : Alphabet) → Functor ℓM Unit (λ _ → tt) tt
DyckCode lp rp = ⊕e Bool (dyckBranch lp rp)

Dyck : Alphabet → Alphabet → TheoryTy (ℓF ℓM) tt
Dyck lp rp = μ (λ _ → DyckCode lp rp) tt

dyck-NIL : {lp rp : Alphabet} → εTy ⊢ Dyck lp rp
dyck-NIL = roll ∘⊢ σ⊕ false ∘⊢ liftTy

dyck-BALANCED : {lp rp : Alphabet}
  → ⟦ dyckBranch lp rp true ⟧TheoryTy (λ _ → Dyck lp rp)
  ⊢ Dyck lp rp
dyck-BALANCED = roll ∘⊢ σ⊕ true
