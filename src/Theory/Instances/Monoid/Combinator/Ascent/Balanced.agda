{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A shift-reduce parser for `S → ( ) | ( S )`, written with the ascent
   combinators -- the minimal example, *before* lookahead.

   Read it against `Combinator/Grammars/Dyck`, which is the same language
   written with `Core`s: the text is nearly identical, and every difference
   is the mirror.  `tok` is `shift`, `seq` is `goto`, and where the top-down
   parser applies a production by `mapP` along a `roll`, this one applies it
   by `reduce` along the production term itself.

   It chooses by `pick`, which runs both alternatives and keeps the first
   that worked -- so it backtracks, and is *not* LR.  `Ascent/Expr` is the
   same construction with `Predict.chooseA`, which observes the class once
   and commits.  This file is kept for the smaller fixpoint (`AFix` at one
   grammar rather than `AFixAll`) and as the before-picture. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Ascent.Balanced where

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)
open import Cubical.Data.FinData using (zero ; suc)
import Cubical.Data.Maybe as MB

data Br : Type where
  lp rp : Br

_≟B_ : (x y : Br) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
lp ≟B lp = Sum.inl Eq.refl
lp ≟B rp = Sum.inr λ ()
rp ≟B lp = Sum.inr λ ()
rp ≟B rp = Sum.inl Eq.refl

open import Theory.Instances.Monoid.Combinator.Incomplete.Base Br _≟B_ ℓ-zero
open import Theory.Instances.Monoid.Residual Br isSetAlphabet
  using (⟦⊗e⟧⁻)
open import Theory.Instances.Monoid.Combinator.Ascent.Base Br _≟B_
  using (module Goto ; _⟜Set_ ; _⊸Set_)

-- The grammar, as a `μ`: `S → ( ) | ( S )`.
private
  Sbr : Bool → Functor ℓM Unit (λ _ → tt) tt
  Sbr false = ⊗e _⊙_ (two (k (literal lp)) (k (literal rp)))
  Sbr true  = ⊗e _⊙_ (two (k (literal lp))
                          (⊗e _⊙_ (two (Var tt) (k (literal rp)))))

  SC : Unit → Functor ℓM Unit (λ _ → tt) tt
  SC _ = ⊕e Bool Sbr

  isSetSbr : (b : Bool) → isSetValued (Sbr b)
  isSetSbr false zero = lift (isSetLiteral lp)
  isSetSbr false (suc zero) = lift (isSetLiteral rp)
  isSetSbr true zero = lift (isSetLiteral lp)
  isSetSbr true (suc zero) zero = lift tt*
  isSetSbr true (suc zero) (suc zero) = lift (isSetLiteral rp)

  isSetSC : (u : Unit) → isSetValued (SC u)
  isSetSC u .fst = lift isSetBool
  isSetSC u .snd = isSetSbr

Sset : TheorySet _ tt
Sset = μ SC tt , isSetμ SC isSetSC tt

S : TheoryTy _ tt
S = ty Sset

-- ...and its two productions, as the terms `reduce` will move the dot along.
leaf : ty (litSet lp ⊗Set litSet rp) ⊢ S
leaf = roll ∘⊢ σ⊕ false
  ∘⊢ ⟦⊗e⟧⁻ (k (literal lp)) (k (literal rp))
  ∘⊢ (liftTy ,⊗ liftTy)

nest : ty (litSet lp ⊗Set (Sset ⊗Set litSet rp)) ⊢ S
nest = roll ∘⊢ σ⊕ true
  ∘⊢ ⟦⊗e⟧⁻ (k (literal lp)) (⊗e _⊙_ (two (Var tt) (k (literal rp))))
  ∘⊢ (liftTy ,⊗ (⟦⊗e⟧⁻ (Var tt) (k (literal rp)) ∘⊢ (liftTy ,⊗ liftTy)))

open Goto MaybeAnswer MaybeCov Sset

-- The parser.  `shift`, `goto`, `reduce`, `<|>` -- nothing else.
parser : ⊤Ty ⊢ Asc (ℓF ℓM) ⟨□⟩ ⟨□⟩ Sset
parser = AFix.fix (ℓF ℓM) Sset step
  where
  step : ty (▷ (AscSet (ℓF ℓM) ⟨□⟩ ⟨□⟩ Sset)) ⊢ Asc (ℓF ℓM) ⟨□⟩ ⟨□⟩ Sset
  step =
    pick
      -- S → ( )
      (reduce leaf ∘⊢ amore
        ∘⊢ goto (litSet rp) (amore ∘⊢ shift lp) (shift rp))
      -- S → ( S )
      (reduce nest ∘⊢ amore
        ∘⊢ goto (Sset ⊗Set litSet rp) (shift lp)
             (goto (litSet rp) (AFix.call (ℓF ℓM) Sset) (aless ∘⊢ shift rp)))

parse : Test S
parse = runA parser

-- ...and it runs.
accepts : String → Bool
accepts w = go (parse w tt)
  where
  go : Maybe S w → Bool
  go (Sum.inl _) = true
  go (Sum.inr _) = false

balanced-yes : passes
  (accepts at
    ( (lp ∷ rp ∷ [])                     ↦ true
    ∷ (lp ∷ lp ∷ rp ∷ rp ∷ [])           ↦ true
    ∷ (lp ∷ lp ∷ lp ∷ rp ∷ rp ∷ rp ∷ []) ↦ true
    ∷ [] ))
balanced-yes = refl

balanced-no : passes
  (accepts at
    ( []                       ↦ false
    ∷ (lp ∷ [])                ↦ false
    ∷ (rp ∷ [])                ↦ false
    ∷ (lp ∷ lp ∷ rp ∷ [])      ↦ false
    ∷ (lp ∷ rp ∷ rp ∷ [])      ↦ false
    ∷ (lp ∷ rp ∷ lp ∷ rp ∷ []) ↦ false
    ∷ [] ))
balanced-no = refl
