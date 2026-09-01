{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The Dyck language as one recursive-descent parser, parametric in the
   answer: one copy serves `Dec`, `Maybe`, `ND` (`Grammars/DyckTests`). -}
open import Cubical.Foundations.Prelude
open import Theory.Instances.Monoid.Grammars.Dyck
  using (Br ; lp ; rp ; _≟_ ; S ; isSetS ; rollS≅)
import Theory.Instances.Monoid.Combinator.Core Br _≟_ as C

module Theory.Instances.Monoid.Combinator.Grammars.Dyck
  (𝒯 : C.AnswerFunctor) where

open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Unit using (tt)

open C public
open Combinators 𝒯 public

ℓG : Level
ℓG = ℓ-max ℓM (ℓ-suc ℓ-zero)

Sset : TheorySet ℓG tt
Sset = S , isSetS

module P = Fix ℓG Sset

-- what the inner `S` is followed by
afterS : TheorySet ℓG tt
afterS = litSet rp ⊗Set Sset

-- what a `(` is followed by
afterLp : TheorySet ℓG tt
afterLp = Sset ⊗Set afterS

step : ty (▷ (ParserSet ℓG ⟨□⟩ ⟨□⟩ Sset)) ⊢ Parser ℓG ⟨□⟩ ⟨□⟩ Sset
step = mapP≅ rollS≅ ∘⊢ ((pmore ∘⊢ nodeP) <|> nil)
  where
  -- `) S`
  tail′ : ty (▷ (ParserSet ℓG ⟨□⟩ ⟨□⟩ Sset)) ⊢ Parser ℓG ⟨▷⟩ ⟨□⟩ afterS
  tail′ = seq Sset (tok rp) P.call

  -- `S ) S`
  mid : ty (▷ (ParserSet ℓG ⟨□⟩ ⟨□⟩ Sset)) ⊢ Parser ℓG ⟨▷⟩ ⟨▷⟩ afterLp
  mid = seq afterS P.call (pless ∘⊢ tail′)

  -- `( S ) S`
  nodeP : ty (▷ (ParserSet ℓG ⟨□⟩ ⟨□⟩ Sset))
    ⊢ Parser ℓG ⟨▷⟩ ⟨□⟩ (litSet lp ⊗Set afterLp)
  nodeP = seq afterLp (tok lp) mid

dyck : ⊤Ty ⊢ ty (Ans Sset)
dyck = P.runFix step
