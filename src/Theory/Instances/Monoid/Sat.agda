{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Sat
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Bool using (Bool ; true ; isSetBool)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Type.HLevels MonEqns Alphabet (λ _ → tt) listPresentation
  using (TheorySet ; isSet⊕ᴰ)
open import Theory.Type.SemanticAction.Base MonEqns Alphabet (λ _ → tt)
  listPresentation using (SemanticAction ; semact-⊕ᴰ' ; semact-pure)

Sat : (Alphabet → Bool) → Type ℓAlph
Sat P = Σ[ c ∈ Alphabet ] (P c ≡ true)

isSetSat : (P : Alphabet → Bool) → isSet (Sat P)
isSetSat P = isSetΣ isSetAlphabet λ _ → isProp→isSet (isSetBool _ _)

satTy : (P : Alphabet → Bool) → TheoryTy ℓM tt
satTy P = ⊕[ x ∈ Sat P ] literal (x .fst)

satSet : (P : Alphabet → Bool) → TheorySet ℓM tt
satSet P =
  satTy P , isSet⊕ᴰ (isSetSat P) λ _ _ → isProp→isSet isPropEqString

-- `satTy P` is a `⊕ᴰ` over the witnesses, so this is that sum's elimination
-- and not a look at the model.
semact-sat : {P : Alphabet → Bool} → SemanticAction (satTy P) Alphabet
semact-sat = semact-⊕ᴰ' λ x → semact-pure (x .fst)
