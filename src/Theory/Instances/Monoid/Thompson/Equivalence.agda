{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Thompson's theorem: the parses of `regex→NFA r` are the parses of `r`.
   Each clause: the construction's iso composed with the connective's congruence. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.WildCat.LocallySmall.Base
open import Cubical.Data.FinSet
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Thompson.Equivalence
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet)
  (isFinSetAlphabet : isFinSet Alphabet)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar.Map Alphabet isSetAlphabet
  using (*≅)
open import Theory.Instances.Monoid.Unitor Alphabet isSetAlphabet using (⊗≅)
open import Theory.Instances.Monoid.Regex.Base Alphabet _≟_ ℓ
  using (RE ; εr ; ⊥r ; ⟨_⟩r ; satr ; _⊗r_ ; _⊕r_ ; _*r)
open import Theory.Instances.Monoid.Automata.NFA.Base Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Thompson.Construction
  Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Thompson.Construction.Sat
  Alphabet isSetAlphabet isFinSetAlphabet using (satNFA≅ ; satG ; ℓsat)
open import Theory.Instances.Monoid.Thompson.Base
  Alphabet isSetAlphabet isFinSetAlphabet _≟_ ℓ
open import Theory.Type.Equivalence.Base MonEqns Alphabet (λ _ → tt)
  listPresentation using (_≅∙_)

open WildCatNotation
open WildCatIso
open NFA
open NFA.Accepting

-- the level a regex's automaton's traces land at
reNFALevel : ∀ {n} → RE n → Level
reNFALevel εr = ℓF ℓM
reNFALevel ⊥r = ℓF ℓM
reNFALevel ⟨ _ ⟩r = ℓF ℓM
reNFALevel (satr _) = ℓF (ℓ-max ℓAlph ℓM)
reNFALevel (r ⊗r r') =
  ℓ-max ℓM (ℓ-max (reNFALevel r) (reNFALevel r'))
reNFALevel (r ⊕r r') = ℓ-max (reNFALevel r) (reNFALevel r')
reNFALevel (r *r) = ℓF (reNFALevel r)

-- `Regex.Base`'s `⟦_⟧`, at the level the traces live at
⟦_⟧nfa : ∀ {n} (r : RE n) → TheoryTy (reNFALevel r) tt
⟦ εr ⟧nfa = LiftTheoryTy (ℓF ℓM) εTy
⟦ ⊥r ⟧nfa = ⊥Ty↑ (ℓF ℓM)
⟦ ⟨ c ⟩r ⟧nfa = LiftTheoryTy (ℓF ℓM) (literal c)
⟦ satr P ⟧nfa = LiftTheoryTy (ℓF (ℓ-max ℓAlph ℓM)) (satG P)
⟦ r ⊗r r' ⟧nfa = ⟦ r ⟧nfa ⊗ ⟦ r' ⟧nfa
⟦ r ⊕r r' ⟧nfa = ⟦ r ⟧nfa ⊕ ⟦ r' ⟧nfa
⟦ r *r ⟧nfa = ⟦ r ⟧nfa *

regex≅NFA : ∀ {n} (r : RE n) → Parse (regex→NFA r) ≅ ⟦ r ⟧nfa
regex≅NFA εr = εNFA≅
regex≅NFA ⊥r = ⊥NFA≅
regex≅NFA ⟨ c ⟩r = litNFA≅ c
regex≅NFA (satr P) = satNFA≅ P
regex≅NFA (r ⊗r r') =
  ⊗NFA≅ (regex→NFA r) (regex→NFA r') ≅∙ ⊗≅ (regex≅NFA r) (regex≅NFA r')
regex≅NFA (r ⊕r r') =
  ⊕NFA≅ (regex→NFA r) (regex→NFA r') ≅∙ ⊕≅ (regex≅NFA r) (regex≅NFA r')
regex≅NFA (r *r) = *NFA≅ (regex→NFA r) ≅∙ *≅ (regex≅NFA r)
