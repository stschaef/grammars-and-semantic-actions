{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Synthesising a `Productions.Table` from a grammar, with the LL(1) check
   computed rather than assumed.

   `Decidable/Productions.Gen` already turns a `Table` into a parser and its
   correctness.  What was missing is the front end: every `Table` in the repo
   is written out by hand, one clause per (nonterminal, class) pair, most of
   them `none`.  Worse, conflict-freedom is only implicit -- `Prod X o` is
   indexed by the class it predicts, so a conflicting table cannot be
   *written*, which means the LL(1) property is enforced by the author rather
   than checked.

   Here a grammar is a list of rules per nonterminal, `clashes` computes the
   LL(1) violations, and `synth` hands back a table only when there are none.

   WHAT DOES NOT ARISE, and why.  There is no FIRST or FOLLOW computation,
   because `led : {c} → List (Item X) → Prod X (tk c)` can only hold a body
   that *begins with a terminal* -- so a body's FIRST set is its leading
   terminal and nothing else, and the LL(1) test collapses to "no nonterminal
   has two rules with the same leading terminal".  Grammars not in that form
   have to be transformed first, which is what `Combinator/LeftCorner` does by
   hand.  Computing *that* transform is the next thing, and it is where FIRST
   and nullability would genuinely be needed. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Decidable.Synthesis
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
  renaming (map to mapL)
import Cubical.Data.Maybe as MB
open import Cubical.Data.Sigma using (_×_ ; _,_)

open import Theory.Instances.Monoid.Combinator.Decidable.Productions
  Alphabet _≟_ public

-- A production in the only form `Prod` can hold one: the terminal that leads
-- it, and the rest of the body.
Rule : Type ℓAlph → Type ℓAlph
Rule X = Alphabet × List (Item X)

-- A grammar: which nonterminals derive ε, and what each one's rules are.
record Rules (X : Type ℓAlph) : Type ℓAlph where
  field
    nullable : X → Bool
    of  : X → List (Rule X)

module _ {X : Type ℓAlph} where

  private
    -- `_≟_` lands in a sum, so every decision is taken by a helper that
    -- receives it; nothing here matches on `with`.
    Dec≟ : Alphabet → Alphabet → Type ℓAlph
    Dec≟ d c = (d Eq.≡ c) Sum.⊎ ((d Eq.≡ c) → Empty.⊥)

  -- the first rule led by `c`, if any
  ruleFor : List (Rule X) → Alphabet → MB.Maybe (List (Item X))
  ruleFor [] c = MB.nothing
  ruleFor ((d , b) ∷ rs) c = go (d ≟ c)
    where
    go : Dec≟ d c → MB.Maybe (List (Item X))
    go (Sum.inl _) = MB.just b
    go (Sum.inr _) = ruleFor rs c

  private
    leads : Alphabet → List (Rule X) → Bool
    leads c [] = false
    leads c ((d , _) ∷ rs) = go (d ≟ c)
      where
      go : Dec≟ d c → Bool
      go (Sum.inl _) = true
      go (Sum.inr _) = leads c rs

    keepIf : Bool → Alphabet → List Alphabet → List Alphabet
    keepIf true c l = c ∷ l
    keepIf false _ l = l

  -- the leading terminals that name more than one rule: the LL(1) violations
  -- of one nonterminal
  dups : List (Rule X) → List Alphabet
  dups [] = []
  dups ((d , _) ∷ rs) = keepIf (leads d rs) d (dups rs)

module Synth {X : Type ℓAlph} (xs : List X) (R : Rules X) where
  open Rules R

  private
    prodFor : List (Rule X) → (o : M₁) → Prod X o
    prodFor rs ε₁ = none
    prodFor rs (tk c) = go (ruleFor rs c)
      where
      go : MB.Maybe (List (Item X)) → Prod X (tk c)
      go MB.nothing = none
      go (MB.just b) = led b

  -- The table.  Total whatever the rules are: it takes the *first* rule for
  -- each class, so `clashes` is what certifies that first means only.
  table : Table X
  table .Table.at x = prodFor (of x)
  table .Table.nul = nullable

  -- THE LL(1) CHECK, computed.  `xs` enumerates the nonterminals; the
  -- alphabet need not be enumerated, because a clash can only happen between
  -- two rules that are both present.
  clashes : List (X × Alphabet)
  clashes = go xs
    where
    go : List X → List (X × Alphabet)
    go [] = []
    go (x ∷ ys) = mapL (x ,_) (dups (of x)) ++ go ys

  -- ...so a table comes back only from a grammar that passes it.
  synth : MB.Maybe (Table X)
  synth = go clashes
    where
    go : List (X × Alphabet) → MB.Maybe (Table X)
    go [] = MB.just table
    go (_ ∷ _) = MB.nothing
