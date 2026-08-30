{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Implicit deterministic automata, ported from `Automata/Implicit.agda`.

   The initial state and the failure state are added *freely* rather than
   being drawn from `Q`.  That is what makes the regex constructions in
   `Implicit/RegExp` compositional: a sub-automaton's states are exactly
   the positions of its sub-expression, so `⊕` and `⊗` just take `⊎` and
   never have to rename or merge anything.  Nullability lives outside `Q`
   as a single `Bool`, because the initial state is not a state.

   `IDA→DA` is then a relabelling -- there is no subset construction
   anywhere in this development, and none is needed: the regexes that
   compile are the deterministic ones, and determinism is exactly the
   side conditions the constructions ask for. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Automaton.Implicit
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Unit using (Unit ; tt ; isSetUnit)
open import Cubical.Foundations.HLevels
import Cubical.Data.Sum as Sum
open Sum using (_⊎_)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Deterministic
  Alphabet isSetAlphabet

private variable ℓ ℓ' : Level

data FreelyAddInitial (Q : Type ℓ) : Type ℓ where
  initial : FreelyAddInitial Q
  ↑i_ : Q → FreelyAddInitial Q

data FreelyAddFail (Q : Type ℓ) : Type ℓ where
  fail : FreelyAddFail Q
  ↑f_ : Q → FreelyAddFail Q

data FreelyAddFail+Initial (Q : Type ℓ) : Type ℓ where
  fail initial : FreelyAddFail+Initial Q
  ↑q_ : Q → FreelyAddFail+Initial Q

FreelyAddFail→FreelyAddFail+Initial : {Q : Type ℓ}
  → FreelyAddFail Q → FreelyAddFail+Initial Q
FreelyAddFail→FreelyAddFail+Initial fail = fail
FreelyAddFail→FreelyAddFail+Initial (↑f q) = ↑q q

↑f→q = FreelyAddFail→FreelyAddFail+Initial

FreelyAddInitial→FreelyAddFail+Initial : {Q : Type ℓ}
  → FreelyAddInitial Q → FreelyAddFail+Initial Q
FreelyAddInitial→FreelyAddFail+Initial initial = initial
FreelyAddInitial→FreelyAddFail+Initial (↑i q) = ↑q q

↑i→q = FreelyAddInitial→FreelyAddFail+Initial

-- `fail` is not in the image of `↑f_`, in the `Eq` world where the
-- transition table's `with`-abstractions leave their equations
fail≢↑f : {Q : Type ℓ} {q : Q} → fail Eq.≡ (↑f q) → Empty.⊥
fail≢↑f ()

mapFreelyAddFail : {X : Type ℓ} {Y : Type ℓ'}
  → (X → Y) → FreelyAddFail X → FreelyAddFail Y
mapFreelyAddFail f fail = fail
mapFreelyAddFail f (↑f x) = ↑f (f x)

mapFreelyAddInitial : {X : Type ℓ} {Y : Type ℓ'}
  → (X → Y) → FreelyAddInitial X → FreelyAddInitial Y
mapFreelyAddInitial f initial = initial
mapFreelyAddInitial f (↑i x) = ↑i (f x)

mapFreelyAddFail+Initial : {X : Type ℓ} {Y : Type ℓ'}
  → (X → Y) → FreelyAddFail+Initial X → FreelyAddFail+Initial Y
mapFreelyAddFail+Initial f fail = fail
mapFreelyAddFail+Initial f initial = initial
mapFreelyAddFail+Initial f (↑q x) = ↑q (f x)

module _ (Q : Type ℓ) where
  open Iso

  FreelyAddFail+Initial≅Unit⊎Unit⊎ :
    Iso (FreelyAddFail+Initial Q) ((Unit ⊎ Unit) ⊎ Q)
  FreelyAddFail+Initial≅Unit⊎Unit⊎ .fun initial = Sum.inl (Sum.inl tt)
  FreelyAddFail+Initial≅Unit⊎Unit⊎ .fun fail = Sum.inl (Sum.inr tt)
  FreelyAddFail+Initial≅Unit⊎Unit⊎ .fun (↑q q) = Sum.inr q
  FreelyAddFail+Initial≅Unit⊎Unit⊎ .inv (Sum.inl (Sum.inl _)) = initial
  FreelyAddFail+Initial≅Unit⊎Unit⊎ .inv (Sum.inl (Sum.inr _)) = fail
  FreelyAddFail+Initial≅Unit⊎Unit⊎ .inv (Sum.inr q) = ↑q q
  FreelyAddFail+Initial≅Unit⊎Unit⊎ .sec (Sum.inl (Sum.inl _)) = refl
  FreelyAddFail+Initial≅Unit⊎Unit⊎ .sec (Sum.inl (Sum.inr _)) = refl
  FreelyAddFail+Initial≅Unit⊎Unit⊎ .sec (Sum.inr _) = refl
  FreelyAddFail+Initial≅Unit⊎Unit⊎ .ret fail = refl
  FreelyAddFail+Initial≅Unit⊎Unit⊎ .ret initial = refl
  FreelyAddFail+Initial≅Unit⊎Unit⊎ .ret (↑q _) = refl

  isSetFreelyAddFail+Initial : isSet Q → isSet (FreelyAddFail+Initial Q)
  isSetFreelyAddFail+Initial isSetQ =
    isSetRetract
      (FreelyAddFail+Initial≅Unit⊎Unit⊎ .fun)
      (FreelyAddFail+Initial≅Unit⊎Unit⊎ .inv)
      (FreelyAddFail+Initial≅Unit⊎Unit⊎ .ret)
      (Sum.isSet⊎ (Sum.isSet⊎ isSetUnit isSetUnit) isSetQ)

record ImplicitDeterministicAutomaton (Q : Type ℓAlph) : Type ℓAlph where
  constructor mkImplicitAut
  field
    acc  : Q → Bool
    null : Bool
    δq   : Q → Alphabet → FreelyAddFail Q
    δᵢ   : Alphabet → FreelyAddFail Q

module _ {Q : Type ℓAlph} (M : ImplicitDeterministicAutomaton Q) where
  open ImplicitDeterministicAutomaton M

  isAcc' : FreelyAddFail+Initial Q → Bool
  isAcc' fail = false
  isAcc' initial = null
  isAcc' (↑q q) = acc q

  δ' : FreelyAddFail+Initial Q → Alphabet → FreelyAddFail+Initial Q
  δ' fail _ = fail
  δ' initial c = ↑f→q (δᵢ c)
  δ' (↑q q) c = ↑f→q (δq q c)

  -- no subset construction: the states are already deterministic
  IDA→DA : DeterministicAutomaton (FreelyAddFail+Initial Q)
  IDA→DA .DeterministicAutomaton.init = initial
  IDA→DA .DeterministicAutomaton.isAcc = isAcc'
  IDA→DA .DeterministicAutomaton.δ = δ'

  -- `fail` is the freely added sink: it rejects and it is absorbing, so
  -- `Trace true fail w` is empty and a scan may exit there.
  failDead : Deadness IDA→DA
  failDead .Deadness.isDead fail = true
  failDead .Deadness.isDead initial = false
  failDead .Deadness.isDead (↑q _) = false
  failDead .Deadness.dead-δ fail _ _ = Eq.refl
  failDead .Deadness.dead-δ initial _ ()
  failDead .Deadness.dead-δ (↑q _) _ ()
  failDead .Deadness.dead-rej fail _ = Eq.refl
  failDead .Deadness.dead-rej initial ()
  failDead .Deadness.dead-rej (↑q _) ()
