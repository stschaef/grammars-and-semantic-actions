{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Configurations at the *real* Dyck grammar.

   An earlier version of this file built a configuration for the single
   string `( ( ) )`, by spelling it out as a tensor of four literals.  That
   was a bad demonstration: the grammar was a singleton, so the whole thing
   recognised a one-word language and the configuration looked like a trace
   of a parse rather than a state.  The fault was the grammar, not `Config`.

   Here the grammar is `Grammars/Dyck`'s `S` -- `S → ε | ( S ) S` -- and
   nothing is hard-coded to any string.  Two things are shown:

     * the ordinary Dyck parser *is* a cut against the empty configuration
       (`dyckByCut≡dyck`, by `refl`), so configurations are not a side
       gadget: `runP` was already one;
     * `push` puts a whole *grammar* on the stack, not a token.  `ctxTwo`
       holds a pending `S`, so cutting the same parser against it accepts
       two concatenated Dyck words. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.MachineDyck where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using ([] ; _∷_)
open import Cubical.Data.Sigma using (_,_)
import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit using (tt ; tt*)

open import Theory.Instances.Monoid.Grammars.Dyck using (Br ; lp ; rp ; _≟_)
import Theory.Instances.Monoid.Combinator.Incomplete.Base Br _≟_ ℓ-zero as Inc
import Theory.Instances.Monoid.Combinator.Machine Br _≟_ as Mch
open import Theory.Instances.Monoid.Combinator.Grammars.Dyck Inc.MaybeAnswer

-- THE REAL PARSER, before it is run: the guarded fixpoint of `step`.
dyckParser : ⊤Ty ⊢ Parser P.ℓ𝒦 ⟨□⟩ ⟨□⟩ Sset
dyckParser = P.fix step

-- ---------------------------------------------------------------------------
-- 1.  `runP` was already a cut.

module R1 = Mch.Runner Inc.MaybeAnswer {ℓK = ℓG} {A = Sset}

dyckByCut : ⊤Ty ⊢ ty (Ans Sset)
dyckByCut = R1.cut ∘⊢ (dyckParser ,& R1.initial)

dyckByCut≡dyck : dyckByCut ≡ dyck
dyckByCut≡dyck = refl

-- ---------------------------------------------------------------------------
-- 2.  A configuration holding a whole grammar.

module R2 = Mch.Runner Inc.MaybeAnswer {ℓK = ℓG} {A = Sset ⊗Set Sset}

-- `push` moves an entire `S` onto the pending stack, so this context expects
-- one Dyck word with another still owed behind it.  Nothing here mentions a
-- string; `K` is a grammar.
ctxTwo : ⊤Ty ⊢ R2.Config _ ⟨□⟩ ⟨□⟩ Sset
ctxTwo = R2.push dyckParser R2.initial ∘⊢ (id⊢ ,& id⊢)

-- the same `dyckParser`, cut against that context: two Dyck words in a row
twoDyck : ⊤Ty ⊢ ty (Ans (Sset ⊗Set Sset))
twoDyck = R2.cut ∘⊢ (dyckParser ,& ctxTwo)

private
  ok? : {ℓA : Level} {A : TheorySet ℓA tt} (m : ↓M tt) → ty (Inc.MaybeSet A) m → Bool
  ok? _ (Sum.inl _) = true
  ok? _ (Sum.inr _) = false

-- The one-word parser accepts every balanced string, as it always did.
oneEmpty   : ok? {A = Sset} _ (dyckByCut [] tt) Eq.≡ true
oneEmpty   = Eq.refl

oneNested  : ok? {A = Sset} _ (dyckByCut (lp ∷ lp ∷ rp ∷ rp ∷ []) tt) Eq.≡ true
oneNested  = Eq.refl

oneUnbal   : ok? {A = Sset} _ (dyckByCut (lp ∷ lp ∷ rp ∷ []) tt) Eq.≡ false
oneUnbal   = Eq.refl

-- ...and against `ctxTwo` the *same* parser accepts a pair of them.
twoAdjacent : ok? {A = Sset ⊗Set Sset} _ (twoDyck (lp ∷ rp ∷ lp ∷ rp ∷ []) tt) Eq.≡ true
twoAdjacent = Eq.refl

twoUnbal : ok? {A = Sset ⊗Set Sset} _ (twoDyck (lp ∷ lp ∷ rp ∷ []) tt) Eq.≡ false
twoUnbal = Eq.refl
