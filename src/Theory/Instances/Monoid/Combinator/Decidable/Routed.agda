{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Predictive choice indexed by the alternatives, not by the cover's cells.

   `Decidable/Lookahead`'s `Predictive.choose` demands one branch per cell,
   so cells with no production need a `⊥Set↑` pad, and a nullable branch
   cannot pay `lead` at all -- which is why `Decidable/Productions` bolts a
   `nul : X → Bool` field and a trailing `<|>` on top.  Here the branches are
   indexed by whatever indexes them (production tags), the cover is reached
   only through `routeIn`, and cells with no branch are `nothing`.

   The nullable case is not repaired by this and cannot be: `E' ::= ε | '+' E`
   followed by another `E'` is genuinely ambiguous, so no route exists at that
   continuation.  Prediction of a nullable branch needs the goal to be indexed
   by its continuation -- the continuation-passed grammar -- not an end over
   continuations.  Until then such a branch is *tried*, by `_<|>_`, which is
   always sound.

   Everything that was once *defined* here -- `Route`, `decM₁`, `PushOf`,
   `Push`, `Choice`, `FixAll` -- turned out not to mention the answer at
   all, so it now lives in `Core` and reaches `Dec` through
   `Decidable/Base`'s `DecCommitting`.  What is left is the name and the
   header. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Decidable.Routed
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Theory.Instances.Monoid.Combinator.Decidable.Base Alphabet _≟_ ℓ public
  hiding (Maybe ; just ; nothing)
