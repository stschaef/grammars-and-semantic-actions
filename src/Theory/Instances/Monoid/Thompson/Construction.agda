{- Thompson's construction, one clause per regex constructor.  Only the
   automaton and its isomorphism are re-exported: the clauses' local
   `fromNFA`/`toNFA`/algebra names would clash. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
module Theory.Instances.Monoid.Thompson.Construction
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Theory.Instances.Monoid.Thompson.Construction.Bottom
  Alphabet isSetAlphabet public using (⊥NFA ; ⊥NFA≅ ; ⊥↑)
open import Theory.Instances.Monoid.Thompson.Construction.Epsilon
  Alphabet isSetAlphabet public using (εNFA ; εNFA≅ ; ε↑)
open import Theory.Instances.Monoid.Thompson.Construction.Literal
  Alphabet isSetAlphabet public using (literalNFA ; litNFA≅ ; STATE≅Fin2)
open import Theory.Instances.Monoid.Thompson.Construction.LinearProduct
  Alphabet isSetAlphabet public using (⊗NFA ; ⊗NFA≅ ; ⊗εTrans-rep ; ⊗State)
open import Theory.Instances.Monoid.Thompson.Construction.Sum
  Alphabet isSetAlphabet public using (⊕NFA ; ⊕NFA≅ ; ⊕State-rep ; ⊕εTrans-rep)
open import Theory.Instances.Monoid.Thompson.Construction.KleeneStar
  Alphabet isSetAlphabet public using (*NFA ; *NFA≅ ; *εTrans-rep)
