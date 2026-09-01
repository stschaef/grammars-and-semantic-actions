{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
-- Soundness at the leaves: ⊥, ε, literal, sat.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Automaton.Implicit.Construction.Leaves
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Cubical.Data.Bool
  using (Bool ; true ; false ; if_then_else_ ; _and_ ; _or_ ; not
        ; isSetBool ; true≢false ; false≢true)
open import Cubical.Data.Unit using (Unit* ; tt ; tt*)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.List using ([] ; _∷_ ; _++_ ; ++-unit-r)
import Cubical.Data.List.Properties as L
open import Cubical.Data.Sigma
  using (Σ-syntax ; _×_ ; _,_ ; fst ; snd ; ΣPathP ; Σ≡Prop)
open import Cubical.Relation.Nullary.Base using (Discrete ; yes ; no)
open import Cubical.WildCat.LocallySmall.Base

open import Theory.Instances.Monoid.Types Alphabet _≟_ using (isSetAlphabet)
open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Type.HLevels MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar.Guarded Alphabet isSetAlphabet
  using (¬Nullable)
open import Theory.Instances.Monoid.KleeneStar.Unambiguous
  Alphabet isSetAlphabet
  using (unambiguous-* ; _∉First_ ; _∉FollowLast_ ; SeqUnambig)
open import Theory.Instances.Monoid.Precise Alphabet isSetAlphabet
  using (splitAgree)
open import Theory.Instances.Monoid.SequentialUnambiguity.Base
  Alphabet isSetAlphabet
  using (#→disjoint ; unambiguous⊗ ; unambiguous⊕)
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (_⟜_ ; ⟜-intro ; ⟜-app ; ⊗ε-unit-l⁻ ; ⊗ε-unit-r⁻ ; ⊗ε-unit-r
        ; ⊗⊕ᴰ-distL ; ⊗⊕ᴰ-distR)
open import Theory.Instances.Monoid.Automaton.Implicit.Analysis
  Alphabet _≟_ ℓ
open import Theory.Instances.Monoid.Automaton.Deterministic
  Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Implicit.Disjointness
  Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Unambiguous
  Alphabet isSetAlphabet
  using (unambiguous-Trace ; unambiguousTrace)
open import Theory.Instances.Monoid.Unitor Alphabet isSetAlphabet
  using (isPropεTy)
open import Theory.Instances.Monoid.Regex.Base Alphabet _≟_ ℓ
  using (RE ; ⟦_⟧ ; εr ; ⊥r ; ⟨_⟩r ; satr ; _⊗r_ ; _⊕r_ ; _*r
        ; Sat ; satG ; satSet)


open WildCatNotation
open WildCatIso
open ImplicitDeterministicAutomaton

private variable
  ℓA ℓB ℓX : Level
  b b' : Bool

module Leaves where
  module _ where
    private
      Mach = ⊥Aut discAlphabet
    open DeterministicAutomaton (IDA→DA Mach)
      using (Trace ; TraceTy ; STOP ; STEP)

    ⊥Carrier : FreelyAddInitial (Empty.⊥* {ℓAlph}) → TheoryTy ℓ-zero tt
    ⊥Carrier initial = ⊥Ty
    ⊥Carrier (↑i ())

    ⊥Alg : ParseAlg Mach ⊥Carrier
    ⊥Alg fail = ParseAlgFail Mach
    ⊥Alg initial =
      ⊕-elim (⊕ᴰ-elim λ c → ⊗⊥↑-annihR {A = ＂ c ＂}) (⊕ᴰ-elim λ ())
      ∘⊢ fromCode Mach true initial
    ⊥Alg (↑q ())

    ⊥Aut→ : Parse Mach ⊢ ⊥Ty
    ⊥Aut→ = recParse Mach ⊥Alg initial

    ⊥Aut← : ⊥Ty ⊢ Parse Mach
    ⊥Aut← = ⊥Ty-elim

  module _ where
    private
      Mach = εAut discAlphabet
    open DeterministicAutomaton (IDA→DA Mach)
      using (Trace ; TraceTy ; STOP ; STEP)

    εCarrier : FreelyAddInitial (Empty.⊥* {ℓAlph}) → TheoryTy ℓM tt
    εCarrier initial = εTy
    εCarrier (↑i ())

    εAlg : ParseAlg Mach εCarrier
    εAlg fail = ParseAlgFail Mach
    εAlg initial =
      ⊕-elim
        (⊕ᴰ-elim λ c → ⊥Ty-elim ∘⊢ ⊗⊥↑-annihR {A = ＂ c ＂})
        (⊕ᴰ-elim λ _ → lowerTy)
      ∘⊢ fromCode Mach true initial
    εAlg (↑q ())

    εAut→ : Parse Mach ⊢ εTy
    εAut→ = recParse Mach εAlg initial

    εAut← : εTy ⊢ Parse Mach
    εAut← = STOP initial ∘⊢ liftTy

  module _ (c : Alphabet) where
    private
      Mach = litAut discAlphabet c
    open DeterministicAutomaton (IDA→DA Mach)
      using (Trace ; TraceTy ; STOP ; STEP)

    litCarrier : FreelyAddInitial (Unit* {ℓAlph}) → TheoryTy ℓM tt
    litCarrier initial = ＂ c ＂
    litCarrier (↑i _) = εTy

    litAlg : ParseAlg Mach litCarrier
    litAlg fail = ParseAlgFail Mach
    litAlg initial =
      ⊕-elim (⊕ᴰ-elim initialStep) (⊕ᴰ-elim λ ())
      ∘⊢ fromCode Mach true initial
      where
      initialStep : (c' : Alphabet)
        → ＂ c' ＂ ⊗ ParseAlgCarrier Mach litCarrier (↑f→q (Mach .δᵢ c')) ⊢ ＂ c ＂
      initialStep c' with discAlphabet c c'
      ... | yes p = J (λ c'' _ → ＂ c'' ＂ ⊗ εTy ⊢ ＂ c ＂) ⊗ε-unit-r p
      ... | no _ = ⊥Ty-elim ∘⊢ ⊗⊥↑-annihR {A = ＂ c' ＂}
    litAlg (↑q _) =
      ⊕-elim
        (⊕ᴰ-elim λ c' → ⊥Ty-elim ∘⊢ ⊗⊥↑-annihR {A = ＂ c' ＂})
        (⊕ᴰ-elim λ _ → lowerTy)
      ∘⊢ fromCode Mach true (↑q tt*)

    litAut→ : Parse Mach ⊢ ＂ c ＂
    litAut← : ＂ c ＂ ⊢ Parse Mach

    litAut→ = recParse Mach litAlg initial
    litAut← = STEP c initial ∘⊢ (id⊢ ,⊗ atState) ∘⊢ ⊗ε-unit-r⁻
      where
      atState : εTy ⊢ Trace true (↑f→q (Mach .δᵢ c))
      atState with discAlphabet c c
      ... | yes _ = STOP (↑q tt*) ∘⊢ liftTy
      ... | no ¬p = Empty.rec (¬p refl)

  module _ (P : Alphabet → Bool) where
    private
      Mach = satAut discAlphabet P
    open DeterministicAutomaton (IDA→DA Mach)
      using (Trace ; TraceTy ; STOP ; STEP)

    satCarrier : FreelyAddInitial (Unit* {ℓAlph}) → TheoryTy ℓM tt
    satCarrier initial = satG P
    satCarrier (↑i _) = εTy

    satAlg : ParseAlg Mach satCarrier
    satAlg fail = ParseAlgFail Mach
    satAlg initial =
      ⊕-elim (⊕ᴰ-elim initialStep) (⊕ᴰ-elim λ ())
      ∘⊢ fromCode Mach true initial
      where
      initialStep : (c' : Alphabet)
        → ＂ c' ＂ ⊗ ParseAlgCarrier Mach satCarrier (↑f→q (Mach .δᵢ c')) ⊢ satG P
      initialStep c' with P c' in eq
      ... | true = σ⊕ (c' , Eq.eqToPath eq) ∘⊢ ⊗ε-unit-r
      ... | false = ⊥Ty-elim ∘⊢ ⊗⊥↑-annihR {A = ＂ c' ＂}
    satAlg (↑q _) =
      ⊕-elim
        (⊕ᴰ-elim λ c' → ⊥Ty-elim ∘⊢ ⊗⊥↑-annihR {A = ＂ c' ＂})
        (⊕ᴰ-elim λ _ → lowerTy)
      ∘⊢ fromCode Mach true (↑q tt*)

    satAut→ : Parse Mach ⊢ satG P
    satAut→ = recParse Mach satAlg initial

    satAut← : satG P ⊢ Parse Mach
    satAut← = ⊕ᴰ-elim λ x → atLetter (x .fst) (x .snd)
      where
      atLetter : (d : Alphabet) → P d ≡ true → ＂ d ＂ ⊢ Parse Mach
      atLetter d pd = STEP d initial ∘⊢ (id⊢ ,⊗ atState) ∘⊢ ⊗ε-unit-r⁻
        where
        atState : εTy ⊢ Trace true (↑f→q (Mach .δᵢ d))
        atState =
          subst
            (λ v → εTy ⊢ Trace true (↑f→q (if v then ↑f tt* else fail)))
            (sym pd)
            (STOP (↑q tt*) ∘⊢ liftTy)

