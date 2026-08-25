{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Incomplete.Dyck where

open import Cubical.Data.List using ([] ; _∷_)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Maybe as M

open import Theory.Instances.Monoid.Grammars.Dyck
  using (Br ; lp ; rp ; _≟_ ; Dyck ; done ; nest
        ; S ; isSetS ; rollS ; unrollS ; semactS)
open import Theory.Instances.Monoid.Combinator.Incomplete.Base
  Br _≟_ (ℓ-suc ℓ-zero)

Sset : TheorySet ℓG tt
Sset = S , isSetS

module P = Fix Sset

-- what the inner `S` is followed by
afterS : TheorySet ℓG tt
afterS = litSet rp ⊗Set Sset

-- what a `(` is followed by
afterLp : TheorySet ℓG tt
afterLp = Sset ⊗Set afterS

-- The same recursive descent as `Decidable/Dyck`, and the same tags; only
-- `mapP` is cheaper, since a failure carries no refutation to transport.
step : ty (▷ (ParserSet ⟨□⟩ ⟨□⟩ Sset)) ⊢ Parser ⟨□⟩ ⟨□⟩ Sset
step = mapP rollS ∘⊢ ((pmore ∘⊢ nodeP) <|> nil)
  where
  -- `) S`
  tail′ : ty (▷ (ParserSet ⟨□⟩ ⟨□⟩ Sset)) ⊢ Parser ⟨▷⟩ ⟨□⟩ afterS
  tail′ = seq Sset (tok rp) P.call

  -- `S ) S`
  mid : ty (▷ (ParserSet ⟨□⟩ ⟨□⟩ Sset)) ⊢ Parser ⟨▷⟩ ⟨▷⟩ afterLp
  mid = seq afterS P.call (pless ∘⊢ tail′)

  -- `( S ) S`
  nodeP : ty (▷ (ParserSet ⟨□⟩ ⟨□⟩ Sset))
    ⊢ Parser ⟨▷⟩ ⟨□⟩ (litSet lp ⊗Set afterLp)
  nodeP = seq afterLp (tok lp) mid

-- Sound but not complete: `nothing` is a refusal, not a refutation
testDyck : Test S
testDyck = P.test step

parseDyck : String → M.Maybe Dyck
parseDyck = observe testDyck (semact-Maybe semactS)

dyck-trees : passes
  (parseDyck at
    ( []                                 ↦ M.just done
    ∷ (lp ∷ rp ∷ [])                     ↦ M.just (nest done done)
    ∷ (lp ∷ rp ∷ lp ∷ rp ∷ [])           ↦ M.just (nest done (nest done done))
    ∷ (lp ∷ lp ∷ rp ∷ rp ∷ [])           ↦ M.just (nest (nest done done) done)
    ∷ (lp ∷ lp ∷ rp ∷ lp ∷ rp ∷ rp ∷ []) ↦
        M.just (nest (nest done (nest done done)) done)
    ∷ (lp ∷ lp ∷ lp ∷ rp ∷ rp ∷ rp ∷ []) ↦
        M.just (nest (nest (nest done done) done) done)
    ∷ [] ))
dyck-trees = refl

dyck-no-trees : passes
  (parseDyck at
    ( (lp ∷ [])                   ↦ M.nothing
    ∷ (rp ∷ [])                   ↦ M.nothing
    ∷ (lp ∷ lp ∷ rp ∷ [])         ↦ M.nothing
    ∷ (lp ∷ rp ∷ rp ∷ [])         ↦ M.nothing
    ∷ [] ))
dyck-no-trees = refl
