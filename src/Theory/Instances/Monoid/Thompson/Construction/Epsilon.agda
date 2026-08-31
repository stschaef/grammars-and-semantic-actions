{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Thompson's construction at `ε`: one state, no transitions, initial and
   accepting.  Its only trace is the one that stops immediately. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.WildCat.LocallySmall.Base
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Thompson.Construction.Epsilon
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Bool using (true ; false)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.FinSet.Properties using (isFinSetUnit)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Automata.NFA.Base Alphabet isSetAlphabet

open WildCatNotation
open WildCatIso
open NFA
open NFA.Accepting

εNFA : NFA ℓ-zero
εNFA .Q = Unit , isFinSetUnit
εNFA .init = tt
εNFA .isAcc _ = true
εNFA .transition = Empty.⊥ , isFinSet⊥
εNFA .src ()
εNFA .dst ()
εNFA .label ()
εNFA .ε-transition = Empty.⊥ , isFinSet⊥
εNFA .ε-src ()
εNFA .ε-dst ()

-- the level a one-state automaton's traces land at
ℓε : Level
ℓε = ℓF (ℓ⋆ ℓ-zero)

ε↑ : TheoryTy ℓε tt
ε↑ = LiftTheoryTy ℓε εTy

εAlg : TraceAlg εNFA λ _ → ε↑
εAlg tt = ⊕ᴰ-elim λ where (stop Eq.refl) → liftTy ∘⊢ lowerTy ∘⊢ lowerTy

εInv : ∀ (q : Unit) → ε↑ ⊢ Trace εNFA q
εInv tt = STOP εNFA Eq.refl ∘⊢ lowerTy

εInv-homo : ∀ q → εInv q ∘⊢ εAlg q ≡ roll ∘⊢ map (TraceTy εNFA q) εInv
εInv-homo tt = ⊕ᴰ≡ _ _ λ where (stop Eq.refl) → refl

εNFA≅ : Parse εNFA ≅ ε↑
εNFA≅ .fun = rec (TraceTy εNFA) εAlg tt
εNFA≅ .inv = εInv tt
εNFA≅ .sec = refl
εNFA≅ .ret = rec-section (TraceTy εNFA) εAlg εInv εInv-homo tt
