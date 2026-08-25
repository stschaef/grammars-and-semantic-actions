{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `list ::= '[' ( n (',' n)* )? ']'`, built entirely from the derived
   combinators.  The point of the example is what is *absent*: no `NT`, no
   `Tag`, no `body : Tag → Code`, no `isSetValued`, no roll/unroll pair.
   Every other grammar in this directory pays that ~60 lines to get a
   repetition; `sepBy` is the whole grammar here. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Decidable.ListLit where

open import Cubical.Data.List using ([] ; _∷_)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Maybe as M

-- three tokens: `[`, `]`, `,`, and a number `n`
data Tok : Type ℓ-zero where
  lb rb cm nm : Tok

_≟T_ : (x y : Tok) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
lb ≟T lb = Sum.inl Eq.refl
rb ≟T rb = Sum.inl Eq.refl
cm ≟T cm = Sum.inl Eq.refl
nm ≟T nm = Sum.inl Eq.refl
lb ≟T rb = Sum.inr λ ()
lb ≟T cm = Sum.inr λ ()
lb ≟T nm = Sum.inr λ ()
rb ≟T lb = Sum.inr λ ()
rb ≟T cm = Sum.inr λ ()
rb ≟T nm = Sum.inr λ ()
cm ≟T lb = Sum.inr λ ()
cm ≟T rb = Sum.inr λ ()
cm ≟T nm = Sum.inr λ ()
nm ≟T lb = Sum.inr λ ()
nm ≟T rb = Sum.inr λ ()
nm ≟T cm = Sum.inr λ ()

open import Theory.Instances.Monoid.Combinator.Decidable.Star Tok _≟T_
  (ℓ-suc ℓ-zero)

-- `n (',' n)*`
items : ⊤Ty ⊢ Parser ℓG ⟨▷⟩ ⟨□⟩ _
items = sepBy ℓG (tok nm) (tok cm)

-- `'[' items? ']'`
listP : ⊤Ty ⊢ Parser ℓG ⟨▷⟩ ⟨□⟩ _
listP = between (tok lb) (box (option items)) (pless ∘⊢ tok rb)

decList : Decidable _
decList = runP ℓG (pmore ∘⊢ listP)

ok? : String → M.Maybe Unit
ok? = observe decList (semact-dec (semact-pure tt))

accepts : passes
  (ok? at
    ( (lb ∷ rb ∷ [])                          ↦ M.just tt
    ∷ (lb ∷ nm ∷ rb ∷ [])                     ↦ M.just tt
    ∷ (lb ∷ nm ∷ cm ∷ nm ∷ rb ∷ [])           ↦ M.just tt
    ∷ (lb ∷ nm ∷ cm ∷ nm ∷ cm ∷ nm ∷ rb ∷ []) ↦ M.just tt
    ∷ [] ))
accepts = refl

rejects : passes
  (ok? at
    ( (lb ∷ [])                     ↦ M.nothing
    ∷ (lb ∷ cm ∷ rb ∷ [])           ↦ M.nothing
    ∷ (lb ∷ nm ∷ cm ∷ rb ∷ [])      ↦ M.nothing
    ∷ (lb ∷ nm ∷ nm ∷ rb ∷ [])      ↦ M.nothing
    ∷ (nm ∷ [])                     ↦ M.nothing
    ∷ [] ))
rejects = refl
