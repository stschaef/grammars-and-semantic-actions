{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Regular expressions: the syntax, its denotation, and its parse trees.

   None of this mentions an answer, and it must not: `Reg` is a datatype, so
   if it lived in the answer-parameterised `Syntax` each instantiation would
   get its own incompatible copy and "the same regex at three answers" could
   not be stated.  `Syntax` supplies the one piece that does depend on the
   answer, the compiler `⟦_⟧P`.

   `Reg` is indexed by a `ParserTag`, which is exactly the nullability of the
   expression: `⟨▷⟩` consumes at least one character, `⟨□⟩` may match `ε`.
   The index is what makes `_*r` total -- `many` needs a guarded element
   parser, so `εr *r` is a type error rather than a machine with an ε-loop
   that has to be broken later. -}
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

-- The parse tree an expression admits is the expression's own shape.

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
