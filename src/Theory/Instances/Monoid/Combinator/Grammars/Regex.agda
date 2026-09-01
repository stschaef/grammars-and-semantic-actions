{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Regex syntax, denotation, parse trees -- answer-independent, so one regex works at every answer.
   The `ParserTag` index is nullability: it makes `_*r` total (`εr *r` is a type error). -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Grammars.Regex
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  where

open import Cubical.Data.List using (List)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit* ; tt ; tt*)

open import Theory.Instances.Monoid.Types Alphabet _≟_
open import Theory.Instances.Monoid.Suffix.Base Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet


infixr 30 _*r
infixr 25 _⊗r_
infixr 20 _⊕r_

data Reg : ParserTag → Type ℓAlph where
  ＂_＂r : Alphabet → Reg ⟨▷⟩
  εr : Reg ⟨□⟩
  _⊗r_ : {t : ParserTag} → Reg ⟨▷⟩ → Reg t → Reg ⟨▷⟩
  _⊕r_ : {t : ParserTag} → Reg t → Reg t → Reg t
  _*r : Reg ⟨▷⟩ → Reg ⟨□⟩
  ↑r_ : Reg ⟨▷⟩ → Reg ⟨□⟩

private variable t : ParserTag

-- The star raises a universe, so the denotation's level is a recursion too.
ℓReg : Reg t → Level
ℓReg ＂ c ＂r = ℓM
ℓReg εr = ℓM
ℓReg (r ⊗r s) = ℓ-max ℓAlph (ℓ-max (ℓReg r) (ℓReg s))
ℓReg (r ⊕r s) = ℓ-max (ℓReg r) (ℓReg s)
ℓReg (r *r) = ℓF (ℓReg r)
ℓReg (↑r r) = ℓReg r

⟦_⟧ : (r : Reg t) → TheorySet (ℓReg r) tt
⟦ ＂ c ＂r ⟧ = litSet c
⟦ εr ⟧ = εSet
⟦ r ⊗r s ⟧ = ⟦ r ⟧ ⊗Set ⟦ s ⟧
⟦ r ⊕r s ⟧ = ⟦ r ⟧ ⊕Set ⟦ s ⟧
⟦ r *r ⟧ = StarSet ⟦ r ⟧
⟦ ↑r r ⟧ = ⟦ r ⟧

Tree : Reg t → Type ℓAlph
Tree ＂ c ＂r = Alphabet
Tree εr = Unit*
Tree (r ⊗r s) = Tree r × Tree s
Tree (r ⊕r s) = Tree r Sum.⊎ Tree s
Tree (r *r) = List (Tree r)
Tree (↑r r) = Tree r

regAct : (r : Reg t) → SemanticAction (ty ⟦ r ⟧) (Tree r)
regAct ＂ c ＂r = semact-map-g (σ⊕ c) semact-char
regAct εr = semact-pure tt*
regAct (r ⊗r s) = semact-⊗₂ (regAct r) (regAct s)
regAct (r ⊕r s) = semact-disjunct (regAct r) (regAct s)
regAct (r *r) = semact-* (regAct r)
regAct (↑r r) = regAct r
