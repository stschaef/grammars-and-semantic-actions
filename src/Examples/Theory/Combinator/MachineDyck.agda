{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The real Dyck grammar `S → ε | ( S ) S`: `runP` is a cut against the empty
   configuration, and `push` puts a whole grammar on the stack, not a token. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Examples.Theory.Combinator.MachineDyck where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using ([] ; _∷_)
open import Cubical.Data.Sigma using (_,_)
import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit using (tt ; tt*)

open import Theory.Instances.Monoid.Grammars.Dyck using (Br ; lp ; rp ; _≟_)
import Theory.Instances.Monoid.Combinator.Incomplete.Base Br _≟_ ℓ-zero as Inc
import Theory.Instances.Monoid.Combinator.Machine Br _≟_ as Mch
open import Theory.Instances.Monoid.Combinator.Grammars.Dyck Inc.MaybeAnswer

dyckParser : ⊤Ty ⊢ Parser P.ℓ𝒦 ⟨□⟩ ⟨□⟩ Sset
dyckParser = P.fix step

module R1 = Mch.Runner Inc.MaybeAnswer {ℓK = ℓG} {A = Sset}

dyckByCut : ⊤Ty ⊢ ty (Ans Sset)
dyckByCut = R1.cut ∘⊢ (dyckParser ,& R1.initial)

-- disabled: `refl` here normalises two guarded-fixpoint parsers
-- against each other, which took 12 GB and did not terminate.  The claim is
-- worth keeping, but it needs a structural proof.
-- dyckByCut≡dyck : dyckByCut ≡ dyck
-- dyckByCut≡dyck = refl

module R2 = Mch.Runner Inc.MaybeAnswer {ℓK = ℓG} {A = Sset ⊗Set Sset}

-- `K` is a grammar: this context owes a second `S` behind the first.
ctxTwo : ⊤Ty ⊢ R2.Config _ ⟨□⟩ ⟨□⟩ Sset
ctxTwo = R2.push dyckParser R2.initial ∘⊢ (id⊢ ,& id⊢)

twoDyck : ⊤Ty ⊢ ty (Ans (Sset ⊗Set Sset))
twoDyck = R2.cut ∘⊢ (dyckParser ,& ctxTwo)

private
  ok? : {ℓA : Level} {A : TheorySet ℓA tt} (m : ↓M tt) → ty (Inc.MaybeSet A) m → Bool
  ok? _ (Sum.inl _) = true
  ok? _ (Sum.inr _) = false

oneEmpty   : ok? {A = Sset} _ (dyckByCut [] tt) Eq.≡ true
oneEmpty   = Eq.refl

oneNested  : ok? {A = Sset} _ (dyckByCut (lp ∷ lp ∷ rp ∷ rp ∷ []) tt) Eq.≡ true
oneNested  = Eq.refl

oneUnbal   : ok? {A = Sset} _ (dyckByCut (lp ∷ lp ∷ rp ∷ []) tt) Eq.≡ false
oneUnbal   = Eq.refl

twoAdjacent : ok? {A = Sset ⊗Set Sset} _ (twoDyck (lp ∷ rp ∷ lp ∷ rp ∷ []) tt) Eq.≡ true
twoAdjacent = Eq.refl

twoUnbal : ok? {A = Sset ⊗Set Sset} _ (twoDyck (lp ∷ lp ∷ rp ∷ []) tt) Eq.≡ false
twoUnbal = Eq.refl
