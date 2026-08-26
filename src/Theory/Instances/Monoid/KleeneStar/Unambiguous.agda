{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Is the star of a deterministic factor unambiguous?

   `*Aut≅` -- that an automaton built by `*Aut` parses exactly `KL* A` --
   is commented out in `Automata/Implicit/RegExp/StrongEquivalences.agda`
   with a note that it needs "an unambiguous-* external lemma akin to the
   ⊗ one".  Nothing in either codebase has it.  This file is the attempt.

   The statement, in the hypotheses `*Aut` already demands:

     ¬Nullable A  →  (∀ c → c ∉FollowLast A ⊎ c ∉First A)  →  unambiguous A
       →  unambiguous (A *)

   It is TRUE, and the argument is short.  Suppose `w` has two
   decompositions into `A`-pieces and take the first place they differ:
   one has a piece `u`, the other a piece `u'` with `u` a proper prefix
   of `u'`.  Write `c` for the letter of `u'` just past `u`.  Then

     - the first decomposition continues after `u` with another piece,
       which begins with `c`, so `c ∈ First A`;
     - `u ∈ A` and `u' = u ++ c… ∈ A`, so `c ∈ FollowLast A`.

   Contradiction with the hypothesis.  The two degenerate cases are
   `¬Nullable A` (no empty piece, so nil-vs-cons is impossible) and
   `unambiguous A` (equal pieces have equal parses). -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.KleeneStar.Unambiguous
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.List using ([] ; _∷_ ; _++_)
open import Cubical.Data.List.Properties using (cons-inj₁ ; cons-inj₂)
open import Cubical.Data.Sigma using (Σ ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.Unit using (tt ; tt*)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar.Guarded Alphabet isSetAlphabet
  using (¬Nullable)
private variable ℓA ℓB : Level

-- `∀ m → isProp (A m)`, as `Theory/Type/Unambiguity/Base` states it; named
-- locally because that module reaches here by two paths.
Unambig : TheoryTy ℓA tt → Type _
Unambig A = (m : String) → isProp (A m)

------------------------------------------------------------------------
-- The two letter-set predicates, as the old `SequentialUnambiguity`
-- states them: a refutation rather than a set.

startsWith : Alphabet → TheoryTy ℓM tt
startsWith c = literal c ⊗ ⊤Ty

_∉First_ : Alphabet → TheoryTy ℓA tt → Type _
c ∉First A = startsWith c & A ⊢ ⊥Ty

-- `c` never continues a complete `A` into a longer `A`
_∉FollowLast_ : Alphabet → TheoryTy ℓA tt → Type _
c ∉FollowLast A = ((A ⊗ startsWith c) & A) ⊢ ⊥Ty

-- ...and the pairing the star construction actually demands
SeqUnambig : TheoryTy ℓA tt → Type _
SeqUnambig A = (c : Alphabet) → (c ∉FollowLast A) Sum.⊎ (c ∉First A)

------------------------------------------------------------------------
-- Levi's lemma: two factorisations of one word are nested.
--
-- Not in the codebase anywhere, and it is the combinatorial half of the
-- argument -- it is what produces the letter `c` that the hypothesis
-- then contradicts.

levi : (u v u' v' : String) → u ++ v ≡ u' ++ v'
  → (Σ[ d ∈ String ] ((u' ≡ u ++ d) × (v ≡ d ++ v')))
  Sum.⊎ (Σ[ d ∈ String ] ((u ≡ u' ++ d) × (v' ≡ d ++ v)))
levi [] v u' v' p = Sum.inl (u' , refl , p)
levi (c ∷ u) v [] v' p = Sum.inr (c ∷ u , refl , sym p)
levi (c ∷ u) v (d ∷ u') v' p with levi u v u' v' (cons-inj₂ p)
... | Sum.inl (e , q , r) =
  Sum.inl (e , cong₂ _∷_ (sym (cons-inj₁ p)) q , r)
... | Sum.inr (e , q , r) =
  Sum.inr (e , cong₂ _∷_ (cons-inj₁ p) q , r)

------------------------------------------------------------------------
-- The goal, and what it still needs.
--
-- The argument, spelled out because it is short and the obstruction is
-- not in it:
--
--   Induct on `m` by length -- legitimate because `¬Nullable A` makes
--   every piece nonempty, so the tail of a `cons` is strictly shorter.
--   Unroll both stars with `unroll*` (`roll-unroll`/`unroll-roll` in
--   `Type/Inductive/Base` make that an iso, so `isProp` transports).
--
--     nil/nil    both are the `εTy` point, which is a proposition.
--     nil/cons   `nil` forces `m ≡ []`, so the cons has an empty piece,
--                which `¬Nullable A` refutes.
--     cons/cons  `levi` nests the two first pieces.  If they are equal,
--                the `A`-parses agree by `Unambig A` and the tails by
--                the induction hypothesis.  Otherwise one piece is
--                `u`, the other `u ++ c ∷ d`; then
--                  * the first decomposition continues after `u` with a
--                    piece beginning `c`, so `startsWith c & A`;
--                  * `u ∈ A` and `u ++ c ∷ d ∈ A`, so
--                    `(A ⊗ startsWith c) & A`.
--                `SeqUnambig` refutes whichever of the two it chose.
--
-- What is missing is none of that.  It is that assembling `cons/cons`
-- into a path needs extensionality for `⊗`: two `(A ⊗ B) m` elements
-- with equal splittings and `PathP`-equal factors are equal.  A
-- splitting here is a `Fin 2 → String`, and `Fin 2` has no definitional
-- η (see `two-η` in `Residual`, and the `two≡` comments in `Strings`),
-- so that is a real lemma rather than `refl`.
--
-- It is the SAME lemma that `unambiguous-Trace` needs, for the same
-- reason -- both are `isProp` of a μ whose step is a tensor.  Landing it
-- once unblocks both, which is why this is left as a hole rather than
-- worked around here.

unambiguous-* : {A : TheoryTy ℓA tt}
  → ¬Nullable A → SeqUnambig A → Unambig A → Unambig (A *)
unambiguous-* nu su ua = {!!}
