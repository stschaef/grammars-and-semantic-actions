{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Shift-reduce parser for `S → ( ) | ( S )`, before lookahead.  `pick`
   runs both alternatives and keeps the first that worked, so it
   backtracks and is NOT LR; `Ascent/Expr` commits via `Predict.chooseA`. -}
open import Theory.Type.SemanticAction.Testing using (_↦_ ; _at_ ; passes ; Case)
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
open SortedSig
open SortedEqns

module Examples.Theory.Combinator.AscentBalanced where

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)
open import Cubical.Data.FinData using (zero ; suc)

open import Theory.Instances.Monoid.Grammars.Dyck using (Br ; lp ; rp)
  renaming (_≟_ to _≟B_)

open import Theory.Instances.Monoid.Combinator.Incomplete.Base Br _≟B_ ℓ-zero
open import Theory.Instances.Monoid.Residual Br isSetAlphabet
  using (⟦⊗e⟧⁻)
open import Theory.Instances.Monoid.Combinator.Ascent.Base Br _≟B_
  using (module Goto ; _⟜Set_ ; _⊸Set_)

-- S → ( ) | ( S )
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

-- the productions, as the terms `reduce` moves the dot along
leaf : ty (litSet lp ⊗Set litSet rp) ⊢ S
leaf = roll ∘⊢ σ⊕ false
  ∘⊢ ⟦⊗e⟧⁻ (k (literal lp)) (k (literal rp))
  ∘⊢ (liftTy ,⊗ liftTy)

nest : ty (litSet lp ⊗Set (Sset ⊗Set litSet rp)) ⊢ S
nest = roll ∘⊢ σ⊕ true
  ∘⊢ ⟦⊗e⟧⁻ (k (literal lp)) (⊗e _⊙_ (two (Var tt) (k (literal rp))))
  ∘⊢ (liftTy ,⊗ (⟦⊗e⟧⁻ (Var tt) (k (literal rp)) ∘⊢ (liftTy ,⊗ liftTy)))

open Goto MaybeAnswer MaybeCov Sset

-- `shift`, `goto`, `reduce`, `<|>` -- nothing else
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
