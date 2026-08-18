{- The free monoid's operation fibres are listable: a string has `length + 1`
   factorisations and the unit has one.  This is the presentation-level fact
   that CYK's inner loop runs on. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Splittings
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List as L using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.ListPresentation Alphabet isSetAlphabet
  using (listPresentation)
open import Theory.Base MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Decidable.Base MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Operation.Base MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Operation.Universal MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Operation.Enumerable MonEqns Alphabet (λ _ → tt) listPresentation

String : Type ℓ-zero
String = ↓M tt

-- a two-slot argument tuple
pair : String → String → interpIn _⊙_ ↓M
pair u v = two u v

-- pushing a letter onto the left factor
consTuple : Alphabet → interpIn _⊙_ ↓M → interpIn _⊙_ ↓M
consTuple c ms = two (c ∷ ms zero) (ms (suc zero))

consFib : (c : Alphabet) {w : String} → Fibre _⊙_ w → Fibre _⊙_ (c ∷ w)
consFib c (ms , e) = consTuple c ms , Eq.ap (c ∷_) e

-- the `length w + 1` factorisations of `w`
splits : (w : String) → List (Fibre _⊙_ w)
splits [] = (pair [] [] , Eq.refl) ∷ []
splits (c ∷ w) = (pair [] (c ∷ w) , Eq.refl) ∷ L.map (consFib c) (splits w)

private
  mem-map : (c : Alphabet) {w : String} {f : Fibre _⊙_ w}
    {l : List (Fibre _⊙_ w)}
    → f ∈ᶠ l → consFib c f ∈ᶠ L.map (consFib c) l
  mem-map c (here q) = here (cong (consTuple c) q)
  mem-map c (there i) = there (mem-map c i)

  -- completeness for tuples already in `pair` form, by recursion on the
  -- left factor
  complete-pair : (u v : String) {w : String}
    (e : op _⊙_ (pair u v) Eq.≡ w) → (pair u v , e) ∈ᶠ splits w
  complete-pair [] [] Eq.refl = here refl
  complete-pair [] (c ∷ v) Eq.refl = here refl
  complete-pair (c ∷ u) v Eq.refl =
    there (mem-map c (complete-pair u v Eq.refl))

-- `pair` is the identity on a two-slot tuple, so the general case reindexes
-- the `pair` case
pairη : (ms : interpIn _⊙_ ↓M) → pair (ms zero) (ms (suc zero)) ≡ ms
pairη ms = funExt λ where
  zero → refl
  (suc zero) → refl

completeSplits : {w : String} (f : Fibre _⊙_ w) → f ∈ᶠ splits w
completeSplits (ms , e) =
  mem-reindex (pairη ms) (complete-pair (ms zero) (ms (suc zero)) e)

enumMul : Enumerable _⊙_
enumMul .fibre = splits
enumMul .complete = completeSplits

-- the unit has exactly one factorisation, and only at the empty string
enumUnit : Enumerable ε·
enumUnit .fibre [] = ((λ ()) , Eq.refl) ∷ []
enumUnit .fibre (_ ∷ _) = []
enumUnit .complete (_ , Eq.refl) = here (funExt λ ())

enumMon : (o : MonOp) → Enumerable o
enumMon ε· = enumUnit
enumMon _⊙_ = enumMul

-- the free monoid's fibres are omniscient
searchMon : (o : MonOp) → Searchable o
searchMon o {A = A} = searchFromOmniscient (omniEnum (enumMon o)) {A = A}

-- `PointwiseDecidableFormers.dec⊗ᵘ-at`, whose hypothesis is on the nose
-- `∀⊗ᵘ[ o ] (λ a → DecTy (A a)) m`.  This is the "listable operation fibre"
-- assumption of `Theory.Type.Inductive.Decidability`, discharged.
dec⊗ᵘ-at-Mon : (o : MonOp) {ℓA : Level} {A : interpIn o (TheoryTy ℓA)}
  (m : ↓M (MonSig .resultSort o))
  → ((ms : interpIn o ↓M) → op o ms Eq.≡ m
       → (a : arities MonSig o) → DecAt (A a) (ms a))
  → DecAt (⊗ᵘ[ o ] A) m
dec⊗ᵘ-at-Mon o {A = A} = searchMon o {A = A}
