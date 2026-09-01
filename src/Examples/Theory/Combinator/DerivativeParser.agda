{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `Derivative/Parser` at `S → x S | ε`: the smallest grammar exercising
   `δ`'s `⊗` rule with non-nullable left factor, the recursive `Var`, and
   a nullable alternative the `Nu` branch must not lose. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Examples.Theory.Combinator.DerivativeParser where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.List using ([] ; _∷_)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)

open import Theory.Instances.Monoid.Combinator.ExprGrammar
open import Theory.Instances.Monoid.Combinator.Core Tk _≟K_
open import Theory.Instances.Monoid.Derivative Tk isSetAlphabet using (Dl)
open import Theory.Instances.Monoid.Residual Tk isSetAlphabet using (⟦⊗e⟧⁻)
open import Theory.Instances.Monoid.Combinator.Derivative.Parser Tk _≟K_

-- S → x S | ε, over the one nonterminal `tt`
Sbody : (x : Unit) → Functor ℓM Unit (λ _ → tt) tt
Sbody tt = ⊕e Bool λ where
  true  → ⊗e _⊙_ (two (k (literal ‵x)) (Var tt))
  false → k εTy

S : Unit → TheoryTy _ tt
S = μ Sbody

-- the derivative at `x`, as a grammar in its own right
DS : Unit → TheoryTy _ tt
DS = D Sbody ‵x

-- `DS` is exactly `Dl ‵x S` ("S with one `x` read"), both directions
S-sound : DS tt ⊢ Dl ‵x (S tt)
S-sound = sound Sbody ‵x tt

S-complete : Dl ‵x (S tt) ⊢ DS tt
S-complete = complete Sbody ‵x tt

-- inhabited: `S` accepts `x`, so `DS` accepts `ε`
private
  oneX : S tt (‵x ∷ [])
  oneX = roll _
    (true , ⟦⊗e⟧⁻ (k (literal ‵x)) (Var tt) _
      (two (‵x ∷ []) [] , Eq.refl
      , (lift Eq.refl , (lift (roll _ (false , lift ((λ ()) , Eq.refl , tt*))) , tt*))))

derived : DS tt []
derived = S-complete [] oneX


-- `S-sound ∘⊢ S-complete ≡ id⊢` is not `Eq.refl`-checkable: `∂`/`√` are
-- `opaque`, so `complete` does not reduce; wants `ind`, not evaluation.

-- two letters exercise iteration: `DSxx`'s frozen constants point at
-- `μ (δ ∘ Sbody)`, not at `S`

xx : String
xx = ‵x ∷ ‵x ∷ []

DSxx : Unit → TheoryTy _ tt
DSxx = D* xx Sbody

private
  twoX : S tt (‵x ∷ ‵x ∷ [])
  twoX = roll _
    (true , ⟦⊗e⟧⁻ (k (literal ‵x)) (Var tt) _
      (two (‵x ∷ []) (‵x ∷ []) , Eq.refl
      , (lift Eq.refl , (lift oneX , tt*))))

  parsedXX : ⌈ xx ⌉ ⊢ S tt
  parsedXX _ Eq.refl = twoX

-- Differentiating twice turns that parse into a null parse of `DSxx`...
nullXX : εTy ⊢ DSxx tt
nullXX = toNull xx Sbody tt parsedXX

-- ...and reading it back off the empty word recovers a parse of `x x`.
backXX : ⌈ xx ⌉ ⊢ S tt
backXX = fromNull xx Sbody tt nullXX
