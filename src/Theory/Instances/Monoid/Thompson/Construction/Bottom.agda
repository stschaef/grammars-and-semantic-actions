{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Thompson's construction at `⊥`: one state, no transitions, and it is not
   accepting, so there is no trace at all. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.WildCat.LocallySmall.Base
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Thompson.Construction.Bottom
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.Properties using (isFinSetUnit)
open import Cubical.Data.Bool using (true ; false)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Automata.NFA.Base Alphabet isSetAlphabet

open WildCatNotation
open WildCatIso
open NFA
open NFA.Accepting

⊥NFA : NFA ℓ-zero
⊥NFA .Q = Unit , isFinSetUnit
⊥NFA .init = tt
⊥NFA .isAcc _ = false
⊥NFA .transition = Empty.⊥ , isFinSet⊥
⊥NFA .src ()
⊥NFA .dst ()
⊥NFA .label ()
⊥NFA .ε-transition = Empty.⊥ , isFinSet⊥
⊥NFA .ε-src ()
⊥NFA .ε-dst ()

ℓ⊥ : Level
ℓ⊥ = ℓF (ℓ⋆ ℓ-zero)

⊥↑ : TheoryTy ℓ⊥ tt
⊥↑ = ⊥Ty↑ ℓ⊥

⊥Alg : TraceAlg ⊥NFA λ _ → ⊥↑
⊥Alg tt = ⊕ᴰ-elim λ where (stop ())

⊥Inv : ∀ (q : Unit) → ⊥↑ ⊢ Trace ⊥NFA q
⊥Inv tt = ⊥Ty↑-elim

⊥Inv-homo : ∀ q → ⊥Inv q ∘⊢ ⊥Alg q ≡ roll ∘⊢ map (TraceTy ⊥NFA q) ⊥Inv
⊥Inv-homo tt = ⊕ᴰ≡ _ _ λ where (stop ())

⊥NFA≅ : Parse ⊥NFA ≅ ⊥↑
⊥NFA≅ .fun = rec (TraceTy ⊥NFA) ⊥Alg tt
⊥NFA≅ .inv = ⊥Inv tt
⊥NFA≅ .sec = ⊥Ty↑-η _ ∙ sym (⊥Ty↑-η id⊢)
⊥NFA≅ .ret = rec-section (TraceTy ⊥NFA) ⊥Alg ⊥Inv ⊥Inv-homo tt
