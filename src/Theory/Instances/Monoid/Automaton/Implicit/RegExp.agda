{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Regular expressions as implicit automata, ported from
   `Automata/Implicit/RegExp.agda`.

   Each construction takes `Q` to a sum of its parts' state sets, so the
   states of the finished automaton are the *positions* of the regular
   expression -- one per literal.  Nothing is merged and nothing is
   renamed, which is why there is no subset construction and no
   Brzozowski derivative in sight.

   What pays for that is the side conditions.  `⊕Aut` wants the two
   branches to have disjoint first sets and not both be nullable;
   `⊗Aut` and `*Aut` want the left factor non-nullable and its follow
   set disjoint from the right's first set.  Those are exactly the
   conditions that make a regular expression *deterministic*, and they
   are demanded as arguments, so a non-deterministic regex simply cannot
   be compiled here. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Automaton.Implicit.RegExp
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Bool using (Bool ; true ; false ; if_then_else_ ; _and_)
open import Cubical.Data.Unit using (Unit* ; tt*)
open import Cubical.Relation.Nullary.Base using (Discrete ; yes ; no)
import Cubical.Data.Sum as Sum
open Sum using (_⊎_)
import Cubical.Data.Empty as Empty

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Implicit Alphabet isSetAlphabet
  public

open ImplicitDeterministicAutomaton

private variable ℓ ℓ' : Level

module _ (discAlpha : Discrete Alphabet) where

  ⊥Aut : ImplicitDeterministicAutomaton (Empty.⊥* {ℓAlph})
  ⊥Aut .acc ()
  ⊥Aut .null = false
  ⊥Aut .δq ()
  ⊥Aut .δᵢ _ = fail

  εAut : ImplicitDeterministicAutomaton (Empty.⊥* {ℓAlph})
  εAut .acc ()
  εAut .null = true
  εAut .δq ()
  εAut .δᵢ _ = fail

  -- one position, reached exactly by its own letter
  litAut : (c : Alphabet) → ImplicitDeterministicAutomaton (Unit* {ℓAlph})
  litAut c .acc _ = true
  litAut c .null = false
  litAut c .δᵢ c' with discAlpha c c'
  ... | yes _ = ↑f _
  ... | no _ = fail
  litAut c .δq _ _ = fail

  -- ...and a character class is the same automaton with a decidable
  -- predicate deciding the entry instead of a single letter.  Its
  -- follow-last set is empty for the same reason: it never steps once
  -- it has accepted.
  satAut : (P : Alphabet → Bool) → ImplicitDeterministicAutomaton (Unit* {ℓAlph})
  satAut P .acc _ = true
  satAut P .null = false
  satAut P .δᵢ c = if P c then ↑f _ else fail
  satAut P .δq _ _ = fail

  -- Alternation: disjoint firsts, and not both nullable.

  module _ {Q Q' : Type ℓAlph}
    (M : ImplicitDeterministicAutomaton Q)
    (M' : ImplicitDeterministicAutomaton Q')
    (notBothNull : (M .null ≡ false) ⊎ (M' .null ≡ false))
    (disjointFirsts :
      (c : Alphabet) → (fail ≡ M .δᵢ c) ⊎ (fail ≡ M' .δᵢ c))
    where

    ⊕Aut : ImplicitDeterministicAutomaton (Q ⊎ Q')
    ⊕Aut .acc (Sum.inl q) = M .acc q
    ⊕Aut .acc (Sum.inr q') = M' .acc q'
    ⊕Aut .null = Sum.rec (λ _ → M' .null) (λ _ → M .null) notBothNull
    ⊕Aut .δq (Sum.inl q) c = mapFreelyAddFail Sum.inl (M .δq q c)
    ⊕Aut .δq (Sum.inr q') c = mapFreelyAddFail Sum.inr (M' .δq q' c)
    ⊕Aut .δᵢ c =
      Sum.rec
        (λ _ → mapFreelyAddFail Sum.inr (M' .δᵢ c))
        (λ _ → mapFreelyAddFail Sum.inl (M .δᵢ c))
        (disjointFirsts c)

  -- Concatenation: the left factor consumes, and its follow set is
  -- disjoint from the right's first set.

  module _ {Q Q' : Type ℓAlph}
    (M : ImplicitDeterministicAutomaton Q)
    (M' : ImplicitDeterministicAutomaton Q')
    (notNullM : M .null ≡ false)
    (seqUnambig :
      (c : Alphabet)
      → ((q : Q) → M .acc q ≡ true → fail ≡ M .δq q c) ⊎ (fail ≡ M' .δᵢ c))
    where

    ⊗Aut : ImplicitDeterministicAutomaton (Q ⊎ Q')
    ⊗Aut .acc (Sum.inl q) = M .acc q and M' .null
    ⊗Aut .acc (Sum.inr q') = M' .acc q'
    ⊗Aut .null = false
    ⊗Aut .δq (Sum.inl q) c =
      if (M .acc q)
      then Sum.rec
             (λ _ → mapFreelyAddFail Sum.inr (M' .δᵢ c))
             (λ _ → mapFreelyAddFail Sum.inl (M .δq q c))
             (seqUnambig c)
      else mapFreelyAddFail Sum.inl (M .δq q c)
    ⊗Aut .δq (Sum.inr q') c = mapFreelyAddFail Sum.inr (M' .δq q' c)
    ⊗Aut .δᵢ c = mapFreelyAddFail Sum.inl (M .δᵢ c)

  -- Star: the same condition against itself, so a loop is unambiguous.

  module _ {Q : Type ℓAlph}
    (M : ImplicitDeterministicAutomaton Q)
    (notNullM : M .null ≡ false)
    (seqUnambig :
      (c : Alphabet)
      → ((q : Q) → M .acc q ≡ true → fail ≡ M .δq q c) ⊎ (fail ≡ M .δᵢ c))
    where

    *Aut : ImplicitDeterministicAutomaton Q
    *Aut .acc q = M .acc q
    *Aut .null = true
    *Aut .δq q c =
      if (M .acc q)
      then Sum.rec (λ _ → M .δᵢ c) (λ _ → M .δq q c) (seqUnambig c)
      else M .δq q c
    *Aut .δᵢ c = M .δᵢ c
