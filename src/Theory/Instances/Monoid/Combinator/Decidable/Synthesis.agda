{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Synthesise a `Productions.Table`, LL(1) check computed rather than assumed.
   No FIRST/FOLLOW arises: `led` only holds bodies beginning with a terminal, so the LL(1)
   test collapses to "no nonterminal has two rules with the same leading terminal"
   (other grammars must be transformed first, as `Combinator/LeftCorner` does by hand). -}
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

Rule : Type ℓAlph → Type ℓAlph
Rule X = Alphabet × List (Item X)

record Rules (X : Type ℓAlph) : Type ℓAlph where
  field
    nullable : X → Bool
    of  : X → List (Rule X)

module _ {X : Type ℓAlph} where

  private
    -- decisions taken by helpers; nothing here matches on `with`
    Dec≟ : Alphabet → Alphabet → Type ℓAlph
    Dec≟ d c = (d Eq.≡ c) Sum.⊎ ((d Eq.≡ c) → Empty.⊥)

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

  -- one nonterminal's LL(1) violations
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

  -- total whatever the rules: takes the *first* rule per class; `clashes` certifies first = only
  table : Table X
  table .Table.at x = prodFor (of x)
  table .Table.nul = nullable

  -- the alphabet need not be enumerated: a clash only happens between rules both present
  clashes : List (X × Alphabet)
  clashes = go xs
    where
    go : List X → List (X × Alphabet)
    go [] = []
    go (x ∷ ys) = mapL (x ,_) (dups (of x)) ++ go ys

  synth : MB.Maybe (Table X)
  synth = go clashes
    where
    go : List (X × Alphabet) → MB.Maybe (Table X)
    go [] = MB.just table
    go (_ ∷ _) = MB.nothing
