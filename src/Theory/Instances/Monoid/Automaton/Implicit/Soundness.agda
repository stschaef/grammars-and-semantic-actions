{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Soundness of `compile`: the automaton compiled from a deterministic
   regular expression parses exactly that expression's language. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Automaton.Implicit.Soundness
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
open import Theory.Instances.Monoid.SequentialUnambiguity.First
  Alphabet isSetAlphabet using (#→disjoint)
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (_⟜_ ; ⟜-intro ; ⟜-app ; ⊗ε-unit-l⁻ ; ⊗ε-unit-r⁻ ; ⊗ε-unit-r
        ; ⊗⊕ᴰ-distL ; ⊗⊕ᴰ-distR)
open import Theory.Instances.Monoid.Automaton.Implicit.Analysis
  Alphabet _≟_ ℓ public
open import Theory.Instances.Monoid.Automaton.Deterministic
  Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Implicit.Disjointness
  Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Unambiguous
  Alphabet isSetAlphabet
  using (unambiguous-Trace ; unambiguousTrace ; isPropεTy ; isPropPathP)
open import Theory.Instances.Monoid.Regex.Base Alphabet _≟_ ℓ
  using (RE ; ⟦_⟧ ; εr ; ⊥r ; ⟨_⟩r ; satr ; _⊗r_ ; _⊕r_ ; _*r
        ; Sat ; satG ; satSet)

open WildCatNotation
open WildCatIso
open ImplicitDeterministicAutomaton

private variable
  ℓA ℓB ℓX : Level
  b b' : Bool

------------------------------------------------------------------------
-- Two maps plus unambiguity of both ends is an iso: this is the old
-- `≈→≅`, and it is why the whole development can stay logical.

≈→≅ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → unambiguous A → unambiguous B → A ⊢ B → B ⊢ A → A ≅ B
≈→≅ uA uB f g .fun = f
≈→≅ uA uB f g .inv = g
≈→≅ uA uB f g .sec = unambiguous→subterminal uB _ _
≈→≅ uA uB f g .ret = unambiguous→subterminal uA _ _

------------------------------------------------------------------------
-- The compiler's discrete alphabet, once.

disc : Discrete Alphabet
disc = discAlphabet

Aut : {¬FL ¬F : ℙ} (dr : DetReg ¬FL ¬F b)
  → ImplicitDeterministicAutomaton (States dr)
Aut dr = compile disc dr

------------------------------------------------------------------------
-- The base cases.

module Leaves where
  module _ where
    private
      Mach = ⊥Aut disc
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
      Mach = εAut disc
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
      Mach = litAut disc c
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
      initialStep c' with disc c c'
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
      atState with disc c c
      ... | yes _ = STOP (↑q tt*) ∘⊢ liftTy
      ... | no ¬p = Empty.rec (¬p refl)

  module _ (P : Alphabet → Bool) where
    private
      Mach = satAut disc P
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

------------------------------------------------------------------------
-- Alternation.  Ported from `Automata/Implicit/RegExp/WeakEquivalences`'s
-- `⊕Aut≈`; no lifting is needed here because every state set in this
-- development sits at `ℓAlph`.

module Alt {Q Q' : Type ℓAlph}
  (M : ImplicitDeterministicAutomaton Q)
  (M' : ImplicitDeterministicAutomaton Q')
  (notBothNull : (M .null ≡ false) Sum.⊎ (M' .null ≡ false))
  (disjointFirsts :
    (c : Alphabet) → (fail ≡ M .δᵢ c) Sum.⊎ (fail ≡ M' .δᵢ c))
  where

  ⊕A : ImplicitDeterministicAutomaton (Q Sum.⊎ Q')
  ⊕A = ⊕Aut disc M M' notBothNull disjointFirsts

  private
    module DM = DeterministicAutomaton (IDA→DA M)
    module DM' = DeterministicAutomaton (IDA→DA M')
    module D⊕ = DeterministicAutomaton (IDA→DA ⊕A)

    Lε : TheoryTy (ℓF ℓM) tt
    Lε = LiftTheoryTy (ℓF ℓM) εTy

    ------------------------------------------------------------------
    -- Into the alternation.

    ⟦_⟧M : FreelyAddInitial Q → TheoryTy _ tt
    ⟦ initial ⟧M = Parse ⊕A
    ⟦ ↑i q ⟧M = D⊕.Trace true (↑q (Sum.inl q))

    ⟦_⟧M' : FreelyAddInitial Q' → TheoryTy _ tt
    ⟦ initial ⟧M' = Parse ⊕A
    ⟦ ↑i q' ⟧M' = D⊕.Trace true (↑q (Sum.inr q'))

    -- the alternation is nullable whenever the branch that is allowed to
    -- be is
    nullFromL : true Eq.≡ M .null → ⊕A .null ≡ true
    nullFromL p = go notBothNull
      where
      go : (x : (M .null ≡ false) Sum.⊎ (M' .null ≡ false))
        → Sum.rec (λ _ → M' .null) (λ _ → M .null) x ≡ true
      go (Sum.inl h) = Empty.rec (true≢false (Eq.eqToPath p ∙ h))
      go (Sum.inr h) = sym (Eq.eqToPath p)

    nullFromR : true Eq.≡ M' .null → ⊕A .null ≡ true
    nullFromR p = go notBothNull
      where
      go : (x : (M .null ≡ false) Sum.⊎ (M' .null ≡ false))
        → Sum.rec (λ _ → M' .null) (λ _ → M .null) x ≡ true
      go (Sum.inl h) = sym (Eq.eqToPath p)
      go (Sum.inr h) = Empty.rec (true≢false (Eq.eqToPath p ∙ h))

    MAlg : ParseAlg M ⟦_⟧M
    MAlg fail = ParseAlgFail M
    MAlg initial =
      ⊕-elim (⊕ᴰ-elim stepM) (⊕ᴰ-elim stopM)
      ∘⊢ fromCode M true initial
      where
      stopM : true Eq.≡ M .null → Lε ⊢ Parse ⊕A
      stopM p =
        subst (λ v → Lε ⊢ D⊕.Trace v initial) (nullFromL p) (D⊕.STOP initial)

      conv : (c : Alphabet)
        → ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δᵢ c))
        ⊢ D⊕.Trace true (↑f→q (⊕A .δᵢ c))
      conv c with disjointFirsts c
      ... | Sum.inl eq =
        J (λ x _ → ParseAlgCarrier M ⟦_⟧M (↑f→q x)
                 ⊢ D⊕.Trace true (↑f→q (mapFreelyAddFail Sum.inr (M' .δᵢ c))))
          ⊥Ty↑-elim eq
      ... | Sum.inr _ = stay
        where
        stay : ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δᵢ c))
             ⊢ D⊕.Trace true (↑f→q (mapFreelyAddFail Sum.inl (M .δᵢ c)))
        stay with M .δᵢ c
        ... | fail = ⊥Ty↑-elim
        ... | ↑f q = id⊢

      stepM : (c : Alphabet)
        → ＂ c ＂ ⊗ ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δᵢ c)) ⊢ Parse ⊕A
      stepM c = D⊕.STEP c initial ∘⊢ (id⊢ ,⊗ conv c)
    MAlg (↑q q) =
      ⊕-elim (⊕ᴰ-elim stepM) (⊕ᴰ-elim stopM)
      ∘⊢ fromCode M true (↑q q)
      where
      stopM : true Eq.≡ M .acc q → Lε ⊢ D⊕.Trace true (↑q (Sum.inl q))
      stopM p =
        subst (λ v → Lε ⊢ D⊕.Trace v (↑q (Sum.inl q)))
          (sym (Eq.eqToPath p)) (D⊕.STOP (↑q (Sum.inl q)))

      conv : (c : Alphabet)
        → ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δq q c))
        ⊢ D⊕.Trace true (↑f→q (mapFreelyAddFail Sum.inl (M .δq q c)))
      conv c with M .δq q c
      ... | fail = ⊥Ty↑-elim
      ... | ↑f q'' = id⊢

      stepM : (c : Alphabet)
        → ＂ c ＂ ⊗ ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δq q c))
        ⊢ D⊕.Trace true (↑q (Sum.inl q))
      stepM c = D⊕.STEP c (↑q (Sum.inl q)) ∘⊢ (id⊢ ,⊗ conv c)

    M'Alg : ParseAlg M' ⟦_⟧M'
    M'Alg fail = ParseAlgFail M'
    M'Alg initial =
      ⊕-elim (⊕ᴰ-elim stepM') (⊕ᴰ-elim stopM')
      ∘⊢ fromCode M' true initial
      where
      stopM' : true Eq.≡ M' .null → Lε ⊢ Parse ⊕A
      stopM' p =
        subst (λ v → Lε ⊢ D⊕.Trace v initial) (nullFromR p) (D⊕.STOP initial)

      conv : (c : Alphabet)
        → ParseAlgCarrier M' ⟦_⟧M' (↑f→q (M' .δᵢ c))
        ⊢ D⊕.Trace true (↑f→q (⊕A .δᵢ c))
      conv c with disjointFirsts c
      ... | Sum.inr eq =
        J (λ x _ → ParseAlgCarrier M' ⟦_⟧M' (↑f→q x)
                 ⊢ D⊕.Trace true (↑f→q (mapFreelyAddFail Sum.inl (M .δᵢ c))))
          ⊥Ty↑-elim eq
      ... | Sum.inl _ = stay
        where
        stay : ParseAlgCarrier M' ⟦_⟧M' (↑f→q (M' .δᵢ c))
             ⊢ D⊕.Trace true (↑f→q (mapFreelyAddFail Sum.inr (M' .δᵢ c)))
        stay with M' .δᵢ c
        ... | fail = ⊥Ty↑-elim
        ... | ↑f q = id⊢

      stepM' : (c : Alphabet)
        → ＂ c ＂ ⊗ ParseAlgCarrier M' ⟦_⟧M' (↑f→q (M' .δᵢ c)) ⊢ Parse ⊕A
      stepM' c = D⊕.STEP c initial ∘⊢ (id⊢ ,⊗ conv c)
    M'Alg (↑q q') =
      ⊕-elim (⊕ᴰ-elim stepM') (⊕ᴰ-elim stopM')
      ∘⊢ fromCode M' true (↑q q')
      where
      stopM' : true Eq.≡ M' .acc q' → Lε ⊢ D⊕.Trace true (↑q (Sum.inr q'))
      stopM' p =
        subst (λ v → Lε ⊢ D⊕.Trace v (↑q (Sum.inr q')))
          (sym (Eq.eqToPath p)) (D⊕.STOP (↑q (Sum.inr q')))

      conv : (c : Alphabet)
        → ParseAlgCarrier M' ⟦_⟧M' (↑f→q (M' .δq q' c))
        ⊢ D⊕.Trace true (↑f→q (mapFreelyAddFail Sum.inr (M' .δq q' c)))
      conv c with M' .δq q' c
      ... | fail = ⊥Ty↑-elim
      ... | ↑f q'' = id⊢

      stepM' : (c : Alphabet)
        → ＂ c ＂ ⊗ ParseAlgCarrier M' ⟦_⟧M' (↑f→q (M' .δq q' c))
        ⊢ D⊕.Trace true (↑q (Sum.inr q'))
      stepM' c = D⊕.STEP c (↑q (Sum.inr q')) ∘⊢ (id⊢ ,⊗ conv c)

    ------------------------------------------------------------------
    -- ...and back out of it.

    ⟦_⟧⊕ : FreelyAddInitial (Q Sum.⊎ Q') → TheoryTy _ tt
    ⟦ initial ⟧⊕ = Parse M ⊕ Parse M'
    ⟦ ↑i (Sum.inl q) ⟧⊕ = DM.Trace true (↑q q)
    ⟦ ↑i (Sum.inr q') ⟧⊕ = DM'.Trace true (↑q q')

    ⊕Alg : ParseAlg ⊕A ⟦_⟧⊕
    ⊕Alg fail = ParseAlgFail ⊕A
    ⊕Alg initial =
      ⊕-elim (⊕ᴰ-elim step⊕) (⊕ᴰ-elim (stop⊕ notBothNull))
      ∘⊢ fromCode ⊕A true initial
      where
      stop⊕ : (y : (M .null ≡ false) Sum.⊎ (M' .null ≡ false))
        → true Eq.≡ Sum.rec (λ _ → M' .null) (λ _ → M .null) y
        → Lε ⊢ Parse M ⊕ Parse M'
      stop⊕ (Sum.inl h) p =
        inr ∘⊢ subst (λ v → Lε ⊢ DM'.Trace v initial)
                 (sym (Eq.eqToPath p)) (DM'.STOP initial)
      stop⊕ (Sum.inr h) p =
        inl ∘⊢ subst (λ v → Lε ⊢ DM.Trace v initial)
                 (sym (Eq.eqToPath p)) (DM.STOP initial)

      step⊕ : (c : Alphabet)
        → ＂ c ＂ ⊗ ParseAlgCarrier ⊕A ⟦_⟧⊕ (↑f→q (⊕A .δᵢ c))
        ⊢ Parse M ⊕ Parse M'
      step⊕ c with disjointFirsts c
      ... | Sum.inl _ = inr ∘⊢ DM'.STEP c initial ∘⊢ (id⊢ ,⊗ helpR)
        where
        helpR : ParseAlgCarrier ⊕A ⟦_⟧⊕
                  (↑f→q (mapFreelyAddFail Sum.inr (M' .δᵢ c)))
              ⊢ DM'.Trace true (↑f→q (M' .δᵢ c))
        helpR with M' .δᵢ c
        ... | fail = ⊥Ty↑-elim
        ... | ↑f q' = id⊢
      ... | Sum.inr _ = inl ∘⊢ DM.STEP c initial ∘⊢ (id⊢ ,⊗ helpL)
        where
        helpL : ParseAlgCarrier ⊕A ⟦_⟧⊕
                  (↑f→q (mapFreelyAddFail Sum.inl (M .δᵢ c)))
              ⊢ DM.Trace true (↑f→q (M .δᵢ c))
        helpL with M .δᵢ c
        ... | fail = ⊥Ty↑-elim
        ... | ↑f q = id⊢
    ⊕Alg (↑q (Sum.inl q)) =
      ⊕-elim (⊕ᴰ-elim step⊕) (⊕ᴰ-elim stop⊕)
      ∘⊢ fromCode ⊕A true (↑q (Sum.inl q))
      where
      stop⊕ : true Eq.≡ M .acc q → Lε ⊢ DM.Trace true (↑q q)
      stop⊕ p =
        subst (λ v → Lε ⊢ DM.Trace v (↑q q))
          (sym (Eq.eqToPath p)) (DM.STOP (↑q q))

      help : (c : Alphabet)
        → ParseAlgCarrier ⊕A ⟦_⟧⊕
            (↑f→q (mapFreelyAddFail Sum.inl (M .δq q c)))
        ⊢ DM.Trace true (↑f→q (M .δq q c))
      help c with M .δq q c
      ... | fail = ⊥Ty↑-elim
      ... | ↑f q'' = id⊢

      step⊕ : (c : Alphabet)
        → ＂ c ＂ ⊗ ParseAlgCarrier ⊕A ⟦_⟧⊕
            (↑f→q (mapFreelyAddFail Sum.inl (M .δq q c)))
        ⊢ DM.Trace true (↑q q)
      step⊕ c = DM.STEP c (↑q q) ∘⊢ (id⊢ ,⊗ help c)
    ⊕Alg (↑q (Sum.inr q')) =
      ⊕-elim (⊕ᴰ-elim step⊕) (⊕ᴰ-elim stop⊕)
      ∘⊢ fromCode ⊕A true (↑q (Sum.inr q'))
      where
      stop⊕ : true Eq.≡ M' .acc q' → Lε ⊢ DM'.Trace true (↑q q')
      stop⊕ p =
        subst (λ v → Lε ⊢ DM'.Trace v (↑q q'))
          (sym (Eq.eqToPath p)) (DM'.STOP (↑q q'))

      help : (c : Alphabet)
        → ParseAlgCarrier ⊕A ⟦_⟧⊕
            (↑f→q (mapFreelyAddFail Sum.inr (M' .δq q' c)))
        ⊢ DM'.Trace true (↑f→q (M' .δq q' c))
      help c with M' .δq q' c
      ... | fail = ⊥Ty↑-elim
      ... | ↑f q'' = id⊢

      step⊕ : (c : Alphabet)
        → ＂ c ＂ ⊗ ParseAlgCarrier ⊕A ⟦_⟧⊕
            (↑f→q (mapFreelyAddFail Sum.inr (M' .δq q' c)))
        ⊢ DM'.Trace true (↑q q')
      step⊕ c = DM'.STEP c (↑q q') ∘⊢ (id⊢ ,⊗ help c)

  ⊕Aut→ : Parse ⊕A ⊢ Parse M ⊕ Parse M'
  ⊕Aut→ = recParse ⊕A ⊕Alg initial

  ⊕Aut← : Parse M ⊕ Parse M' ⊢ Parse ⊕A
  ⊕Aut← =
    ⊕-elim (recParse M MAlg initial)
           (recParse M' M'Alg initial)

------------------------------------------------------------------------
-- Concatenation.  The left factor's trace is interpreted in continuation
-- style -- `- ⟜ Parse M'` -- so the right factor is spliced in exactly
-- where the left one accepts.

module Seq {Q Q' : Type ℓAlph}
  (M : ImplicitDeterministicAutomaton Q)
  (M' : ImplicitDeterministicAutomaton Q')
  (notNullM : M .null ≡ false)
  (seqUnambig :
    (c : Alphabet)
    → ((q : Q) → M .acc q ≡ true → fail ≡ M .δq q c)
      Sum.⊎ (fail ≡ M' .δᵢ c))
  where

  ⊗A : ImplicitDeterministicAutomaton (Q Sum.⊎ Q')
  ⊗A = ⊗Aut disc M M' notNullM seqUnambig

  private
    module DM = DeterministicAutomaton (IDA→DA M)
    module DM' = DeterministicAutomaton (IDA→DA M')
    module D⊗ = DeterministicAutomaton (IDA→DA ⊗A)

    Lε : TheoryTy (ℓF ℓM) tt
    Lε = LiftTheoryTy (ℓF ℓM) εTy

    and-l : {x y : Bool} → true Eq.≡ (x and y) → x ≡ true
    and-l {true} _ = refl
    and-l {false} p = Empty.rec (true≢false (Eq.eqToPath p))

    and-r : {x y : Bool} → true Eq.≡ (x and y) → y ≡ true
    and-r {true} p = sym (Eq.eqToPath p)
    and-r {false} p = Empty.rec (true≢false (Eq.eqToPath p))

    ------------------------------------------------------------------
    -- The right factor, as what to do once the left one has accepted.

    ⟦_⟧M' : FreelyAddInitial Q' → TheoryTy _ tt
    ⟦ initial ⟧M' =
      &[ q ∈ Q ] &[ _ ∈ true Eq.≡ M .acc q ] D⊗.Trace true (↑q (Sum.inl q))
    ⟦ ↑i q' ⟧M' = D⊗.Trace true (↑q (Sum.inr q'))

    M'Alg : ParseAlg M' ⟦_⟧M'
    M'Alg fail = ParseAlgFail M'
    M'Alg initial =
      ⊕-elim (⊕ᴰ-elim stepM') (⊕ᴰ-elim stopM')
      ∘⊢ fromCode M' true initial
      where
      stopM' : true Eq.≡ M' .null → Lε ⊢ ⟦ initial ⟧M'
      stopM' p = &ᴰ-intro λ q → &ᴰ-intro λ accEq →
        subst (λ v → Lε ⊢ D⊗.Trace v (↑q (Sum.inl q)))
          (cong₂ _and_ (sym (Eq.eqToPath accEq)) (sym (Eq.eqToPath p)))
          (D⊗.STOP (↑q (Sum.inl q)))

      jump : (c : Alphabet)
        → ParseAlgCarrier M' ⟦_⟧M' (↑f→q (M' .δᵢ c))
        ⊢ D⊗.Trace true (↑f→q (mapFreelyAddFail Sum.inr (M' .δᵢ c)))
      jump c with M' .δᵢ c
      ... | fail = ⊥Ty↑-elim
      ... | ↑f q' = id⊢

      contra : (c : Alphabet) (q : Q) → fail ≡ M' .δᵢ c
        → ParseAlgCarrier M' ⟦_⟧M' (↑f→q (M' .δᵢ c))
        ⊢ D⊗.Trace true (↑f→q (mapFreelyAddFail Sum.inl (M .δq q c)))
      contra c q eq with M' .δᵢ c
      ... | fail = ⊥Ty↑-elim
      ... | ↑f q' = Empty.rec (fail≢↑f (Eq.pathToEq eq))

      nextBase : (c : Alphabet) (q : Q)
        → ParseAlgCarrier M' ⟦_⟧M' (↑f→q (M' .δᵢ c))
        ⊢ D⊗.Trace true (↑f→q
            (Sum.rec (λ _ → mapFreelyAddFail Sum.inr (M' .δᵢ c))
                     (λ _ → mapFreelyAddFail Sum.inl (M .δq q c))
                     (seqUnambig c)))
      nextBase c q with seqUnambig c
      ... | Sum.inl _ = jump c
      ... | Sum.inr eq = contra c q eq

      next : (c : Alphabet) (q : Q) (accEq : true Eq.≡ M .acc q)
        → ParseAlgCarrier M' ⟦_⟧M' (↑f→q (M' .δᵢ c))
        ⊢ D⊗.Trace true (↑f→q (⊗A .δq (Sum.inl q) c))
      next c q accEq =
        subst
          (λ v → ParseAlgCarrier M' ⟦_⟧M' (↑f→q (M' .δᵢ c))
               ⊢ D⊗.Trace true (↑f→q
                   (if v
                    then Sum.rec (λ _ → mapFreelyAddFail Sum.inr (M' .δᵢ c))
                                 (λ _ → mapFreelyAddFail Sum.inl (M .δq q c))
                                 (seqUnambig c)
                    else mapFreelyAddFail Sum.inl (M .δq q c))))
          (Eq.eqToPath accEq)
          (nextBase c q)

      stepM' : (c : Alphabet)
        → ＂ c ＂ ⊗ ParseAlgCarrier M' ⟦_⟧M' (↑f→q (M' .δᵢ c))
        ⊢ ⟦ initial ⟧M'
      stepM' c = &ᴰ-intro λ q → &ᴰ-intro λ accEq →
        D⊗.STEP c (↑q (Sum.inl q)) ∘⊢ (id⊢ ,⊗ next c q accEq)
    M'Alg (↑q q') =
      ⊕-elim (⊕ᴰ-elim stepM') (⊕ᴰ-elim stopM')
      ∘⊢ fromCode M' true (↑q q')
      where
      stopM' : true Eq.≡ M' .acc q' → Lε ⊢ D⊗.Trace true (↑q (Sum.inr q'))
      stopM' p =
        subst (λ v → Lε ⊢ D⊗.Trace v (↑q (Sum.inr q')))
          (sym (Eq.eqToPath p)) (D⊗.STOP (↑q (Sum.inr q')))

      help : (c : Alphabet)
        → ParseAlgCarrier M' ⟦_⟧M' (↑f→q (M' .δq q' c))
        ⊢ D⊗.Trace true (↑f→q (mapFreelyAddFail Sum.inr (M' .δq q' c)))
      help c with M' .δq q' c
      ... | fail = ⊥Ty↑-elim
      ... | ↑f q'' = id⊢

      stepM' : (c : Alphabet)
        → ＂ c ＂ ⊗ ParseAlgCarrier M' ⟦_⟧M' (↑f→q (M' .δq q' c))
        ⊢ D⊗.Trace true (↑q (Sum.inr q'))
      stepM' c = D⊗.STEP c (↑q (Sum.inr q')) ∘⊢ (id⊢ ,⊗ help c)

    M'→⊗A : Parse M' ⊢ ⟦ initial ⟧M'
    M'→⊗A = recParse M' M'Alg initial

    ------------------------------------------------------------------
    -- The left factor, in continuation-passing form.

    ⟦_⟧M : FreelyAddInitial Q → TheoryTy _ tt
    ⟦ initial ⟧M = Parse ⊗A ⟜ Parse M'
    ⟦ ↑i q ⟧M = D⊗.Trace true (↑q (Sum.inl q)) ⟜ Parse M'

    MAlg : ParseAlg M ⟦_⟧M
    MAlg fail = ParseAlgFail M
    MAlg initial =
      ⊕-elim (⊕ᴰ-elim stepM)
        (⊕ᴰ-elim λ p → Empty.rec (true≢false (Eq.eqToPath p ∙ notNullM)))
      ∘⊢ fromCode M true initial
      where
      conv : (c : Alphabet)
        → ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δᵢ c)) ⊗ Parse M'
        ⊢ D⊗.Trace true (↑f→q (mapFreelyAddFail Sum.inl (M .δᵢ c)))
      conv c with M .δᵢ c
      ... | fail = ⊥Ty-elim ∘⊢ ⊗⊥↑-annihL {A = Parse M'}
      ... | ↑f q'' = ⟜-app

      stepM : (c : Alphabet)
        → ＂ c ＂ ⊗ ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δᵢ c))
        ⊢ Parse ⊗A ⟜ Parse M'
      stepM c =
        ⟜-intro (D⊗.STEP c initial ∘⊢ (id⊢ ,⊗ conv c) ∘⊢ ⊗-assoc)
    MAlg (↑q q) =
      ⊕-elim (⊕ᴰ-elim stepM) (⊕ᴰ-elim stopM)
      ∘⊢ fromCode M true (↑q q)
      where
      stopM : true Eq.≡ M .acc q
        → Lε ⊢ D⊗.Trace true (↑q (Sum.inl q)) ⟜ Parse M'
      stopM x =
        ⟜-intro (π x ∘⊢ π q ∘⊢ M'→⊗A ∘⊢ ⊗-unit-l ∘⊢ (lowerTy ,⊗ id⊢))

      stay : (c : Alphabet)
        → ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δq q c)) ⊗ Parse M'
        ⊢ D⊗.Trace true (↑f→q (mapFreelyAddFail Sum.inl (M .δq q c)))
      stay c with M .δq q c
      ... | fail = ⊥Ty-elim ∘⊢ ⊗⊥↑-annihL {A = Parse M'}
      ... | ↑f q'' = ⟜-app

      contra : (c : Alphabet)
        → ((q : Q) → M .acc q ≡ true → fail ≡ M .δq q c)
        → M .acc q Eq.≡ true
        → ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δq q c)) ⊗ Parse M'
        ⊢ D⊗.Trace true (↑f→q (mapFreelyAddFail Sum.inr (M' .δᵢ c)))
      contra c h accEq with M .δq q c in dqEq
      ... | fail = ⊥Ty-elim ∘⊢ ⊗⊥↑-annihL {A = Parse M'}
      ... | ↑f q'' =
        Empty.rec
          (fail≢↑f
            (Eq.pathToEq (h q (Eq.eqToPath accEq) ∙ Eq.eqToPath dqEq)))

      conv : (c : Alphabet)
        → ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δq q c)) ⊗ Parse M'
        ⊢ D⊗.Trace true (↑f→q (⊗A .δq (Sum.inl q) c))
      conv c with M .acc q in accEq
      ... | false = stay c
      ... | true with seqUnambig c
      ...   | Sum.inr _ = stay c
      ...   | Sum.inl h = contra c h accEq

      stepM : (c : Alphabet)
        → ＂ c ＂ ⊗ ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δq q c))
        ⊢ D⊗.Trace true (↑q (Sum.inl q)) ⟜ Parse M'
      stepM c =
        ⟜-intro
          (D⊗.STEP c (↑q (Sum.inl q)) ∘⊢ (id⊢ ,⊗ conv c) ∘⊢ ⊗-assoc)

    ------------------------------------------------------------------
    -- ...and back: a trace of the concatenation splits at the join.

    ⟦_⟧⊗ : FreelyAddInitial (Q Sum.⊎ Q') → TheoryTy _ tt
    ⟦ initial ⟧⊗ = Parse M ⊗ Parse M'
    ⟦ ↑i (Sum.inl q) ⟧⊗ = DM.Trace true (↑q q) ⊗ Parse M'
    ⟦ ↑i (Sum.inr q') ⟧⊗ = DM'.Trace true (↑q q')

    ⊗Alg : ParseAlg ⊗A ⟦_⟧⊗
    ⊗Alg fail = ParseAlgFail ⊗A
    ⊗Alg initial =
      ⊕-elim (⊕ᴰ-elim step⊗)
        (⊕ᴰ-elim λ x → Empty.rec (true≢false (Eq.eqToPath x)))
      ∘⊢ fromCode ⊗A true initial
      where
      helpInit : (c : Alphabet)
        → ParseAlgCarrier ⊗A ⟦_⟧⊗
            (↑f→q (mapFreelyAddFail Sum.inl (M .δᵢ c)))
        ⊢ DM.Trace true (↑f→q (M .δᵢ c)) ⊗ Parse M'
      helpInit c with M .δᵢ c
      ... | fail = ⊥Ty↑-elim
      ... | ↑f q = id⊢

      step⊗ : (c : Alphabet)
        → ＂ c ＂ ⊗ ParseAlgCarrier ⊗A ⟦_⟧⊗
            (↑f→q (mapFreelyAddFail Sum.inl (M .δᵢ c)))
        ⊢ Parse M ⊗ Parse M'
      step⊗ c =
        (DM.STEP c initial ,⊗ id⊢) ∘⊢ ⊗-assoc⁻ ∘⊢ (id⊢ ,⊗ helpInit c)
    ⊗Alg (↑q (Sum.inl q)) =
      ⊕-elim (⊕ᴰ-elim step⊗) (⊕ᴰ-elim stop⊗)
      ∘⊢ fromCode ⊗A true (↑q (Sum.inl q))
      where
      stop⊗ : true Eq.≡ (M .acc q and M' .null)
        → Lε ⊢ DM.Trace true (↑q q) ⊗ Parse M'
      stop⊗ x = (tA ,⊗ tN) ∘⊢ ⊗ε-unit-l⁻ ∘⊢ lowerTy
        where
        tA : εTy ⊢ DM.Trace true (↑q q)
        tA = subst (λ v → εTy ⊢ DM.Trace v (↑q q)) (and-l x)
               (DM.STOP (↑q q) ∘⊢ liftTy)

        tN : εTy ⊢ Parse M'
        tN = subst (λ v → εTy ⊢ DM'.Trace v initial) (and-r x)
               (DM'.STOP initial ∘⊢ liftTy)

      helpStay : (c : Alphabet)
        → ParseAlgCarrier ⊗A ⟦_⟧⊗
            (↑f→q (mapFreelyAddFail Sum.inl (M .δq q c)))
        ⊢ DM.Trace true (↑f→q (M .δq q c)) ⊗ Parse M'
      helpStay c with M .δq q c
      ... | fail = ⊥Ty↑-elim
      ... | ↑f q'' = id⊢

      stayStep : (c : Alphabet)
        → ＂ c ＂ ⊗ ParseAlgCarrier ⊗A ⟦_⟧⊗
            (↑f→q (mapFreelyAddFail Sum.inl (M .δq q c)))
        ⊢ DM.Trace true (↑q q) ⊗ Parse M'
      stayStep c =
        (DM.STEP c (↑q q) ,⊗ id⊢) ∘⊢ ⊗-assoc⁻ ∘⊢ (id⊢ ,⊗ helpStay c)

      helpJump : (c : Alphabet)
        → ParseAlgCarrier ⊗A ⟦_⟧⊗
            (↑f→q (mapFreelyAddFail Sum.inr (M' .δᵢ c)))
        ⊢ DM'.Trace true (↑f→q (M' .δᵢ c))
      helpJump c with M' .δᵢ c
      ... | fail = ⊥Ty↑-elim
      ... | ↑f q' = id⊢

      jumpStep : (c : Alphabet) → M .acc q Eq.≡ true
        → ＂ c ＂ ⊗ ParseAlgCarrier ⊗A ⟦_⟧⊗
            (↑f→q (mapFreelyAddFail Sum.inr (M' .δᵢ c)))
        ⊢ DM.Trace true (↑q q) ⊗ Parse M'
      jumpStep c accEq =
        (tA ,⊗ DM'.STEP c initial) ∘⊢ ⊗ε-unit-l⁻ ∘⊢ (id⊢ ,⊗ helpJump c)
        where
        tA : εTy ⊢ DM.Trace true (↑q q)
        tA = subst (λ v → εTy ⊢ DM.Trace v (↑q q)) (Eq.eqToPath accEq)
               (DM.STOP (↑q q) ∘⊢ liftTy)

      step⊗ : (c : Alphabet)
        → ＂ c ＂ ⊗ ParseAlgCarrier ⊗A ⟦_⟧⊗
            (↑f→q (⊗A .δq (Sum.inl q) c))
        ⊢ DM.Trace true (↑q q) ⊗ Parse M'
      step⊗ c with M .acc q in accEq
      ... | false = stayStep c
      ... | true with seqUnambig c
      ...   | Sum.inr _ = stayStep c
      ...   | Sum.inl _ = jumpStep c accEq
    ⊗Alg (↑q (Sum.inr q')) =
      ⊕-elim (⊕ᴰ-elim step⊗) (⊕ᴰ-elim stop⊗)
      ∘⊢ fromCode ⊗A true (↑q (Sum.inr q'))
      where
      stop⊗ : true Eq.≡ M' .acc q' → Lε ⊢ DM'.Trace true (↑q q')
      stop⊗ x =
        subst (λ v → Lε ⊢ DM'.Trace v (↑q q'))
          (sym (Eq.eqToPath x)) (DM'.STOP (↑q q'))

      help : (c : Alphabet)
        → ParseAlgCarrier ⊗A ⟦_⟧⊗
            (↑f→q (mapFreelyAddFail Sum.inr (M' .δq q' c)))
        ⊢ DM'.Trace true (↑f→q (M' .δq q' c))
      help c with M' .δq q' c
      ... | fail = ⊥Ty↑-elim
      ... | ↑f q'' = id⊢

      step⊗ : (c : Alphabet)
        → ＂ c ＂ ⊗ ParseAlgCarrier ⊗A ⟦_⟧⊗
            (↑f→q (mapFreelyAddFail Sum.inr (M' .δq q' c)))
        ⊢ DM'.Trace true (↑q q')
      step⊗ c = DM'.STEP c (↑q q') ∘⊢ (id⊢ ,⊗ help c)

  ⊗Aut→ : Parse ⊗A ⊢ Parse M ⊗ Parse M'
  ⊗Aut→ = recParse ⊗A ⊗Alg initial

  ⊗Aut← : Parse M ⊗ Parse M' ⊢ Parse ⊗A
  ⊗Aut← = ⟜-app ∘⊢ (recParse M MAlg initial ,⊗ id⊢)

------------------------------------------------------------------------
-- Star.  `Paste` is what a `KL*` needs and a `⊗` does not: a whole
-- further `Parse *A` re-entered at an accepting state of the body.

private
  star-nil⁻ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
    → ⟦ starBranch A false ⟧TheoryTy (λ _ → B)
    ⊢ LiftTheoryTy (ℓF ℓM) εTy
  star-nil⁻ m (ms , e , _) = lift (ms , e , tt*)

  star-cons⁻ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
    → ⟦ starBranch A true ⟧TheoryTy (λ _ → B) ⊢ A ⊗ B
  star-cons⁻ m (ms , e , f) =
    ms , e , (f zero .lower , (f (suc zero) .lower , tt*))

module Kleene {Q : Type ℓAlph}
  (M : ImplicitDeterministicAutomaton Q)
  (notNullM : M .null ≡ false)
  (seqUnambig :
    (c : Alphabet)
    → ((q : Q) → M .acc q ≡ true → fail ≡ M .δq q c)
      Sum.⊎ (fail ≡ M .δᵢ c))
  where

  *A : ImplicitDeterministicAutomaton Q
  *A = *Aut disc M notNullM seqUnambig

  private
    module DM = DeterministicAutomaton (IDA→DA M)
    module D* = DeterministicAutomaton (IDA→DA *A)

    Lε : TheoryTy (ℓF ℓM) tt
    Lε = LiftTheoryTy (ℓF ℓM) εTy

    ------------------------------------------------------------------
    -- Splicing a further run in at an accepting state.

    module Paste (q : Q) (accEq : true Eq.≡ M .acc q) where
      ⟦_⟧P : FreelyAddInitial Q → TheoryTy _ tt
      ⟦ initial ⟧P = D*.Trace true (↑q q)
      ⟦ ↑i q' ⟧P = D*.Trace true (↑q q')

      pasteAlg : ParseAlg *A ⟦_⟧P
      pasteAlg fail = ParseAlgFail *A
      pasteAlg initial =
        ⊕-elim (⊕ᴰ-elim stepP) (⊕ᴰ-elim λ _ → atAcc)
        ∘⊢ fromCode *A true initial
        where
        atAcc : Lε ⊢ D*.Trace true (↑q q)
        atAcc =
          subst (λ v → Lε ⊢ D*.Trace v (↑q q))
            (sym (Eq.eqToPath accEq)) (D*.STOP (↑q q))

        stay : (c : Alphabet)
          → ParseAlgCarrier *A ⟦_⟧P (↑f→q (M .δᵢ c))
          ⊢ D*.Trace true (↑f→q (M .δᵢ c))
        stay c with M .δᵢ c
        ... | fail = ⊥Ty↑-elim
        ... | ↑f q'' = id⊢

        contra : (c : Alphabet) → fail ≡ M .δᵢ c
          → ParseAlgCarrier *A ⟦_⟧P (↑f→q (M .δᵢ c))
          ⊢ D*.Trace true (↑f→q (M .δq q c))
        contra c eq with M .δᵢ c
        ... | fail = ⊥Ty↑-elim
        ... | ↑f q'' = Empty.rec (fail≢↑f (Eq.pathToEq eq))

        base : (c : Alphabet)
          → ParseAlgCarrier *A ⟦_⟧P (↑f→q (M .δᵢ c))
          ⊢ D*.Trace true (↑f→q
              (Sum.rec (λ _ → M .δᵢ c) (λ _ → M .δq q c) (seqUnambig c)))
        base c with seqUnambig c
        ... | Sum.inl _ = stay c
        ... | Sum.inr eq = contra c eq

        conv : (c : Alphabet)
          → ParseAlgCarrier *A ⟦_⟧P (↑f→q (M .δᵢ c))
          ⊢ D*.Trace true (↑f→q (*A .δq q c))
        conv c =
          subst
            (λ v → ParseAlgCarrier *A ⟦_⟧P (↑f→q (M .δᵢ c))
                 ⊢ D*.Trace true (↑f→q
                     (if v
                      then Sum.rec (λ _ → M .δᵢ c) (λ _ → M .δq q c)
                             (seqUnambig c)
                      else M .δq q c)))
            (Eq.eqToPath accEq)
            (base c)

        stepP : (c : Alphabet)
          → ＂ c ＂ ⊗ ParseAlgCarrier *A ⟦_⟧P (↑f→q (M .δᵢ c))
          ⊢ D*.Trace true (↑q q)
        stepP c = D*.STEP c (↑q q) ∘⊢ (id⊢ ,⊗ conv c)
      pasteAlg (↑q q') =
        ⊕-elim (⊕ᴰ-elim stepP) (⊕ᴰ-elim stopP)
        ∘⊢ fromCode *A true (↑q q')
        where
        stopP : true Eq.≡ M .acc q' → Lε ⊢ D*.Trace true (↑q q')
        stopP x =
          subst (λ v → Lε ⊢ D*.Trace v (↑q q'))
            (sym (Eq.eqToPath x)) (D*.STOP (↑q q'))

        relay : (c : Alphabet)
          → ParseAlgCarrier *A ⟦_⟧P (↑f→q (*A .δq q' c))
          ⊢ D*.Trace true (↑f→q (*A .δq q' c))
        relay c with *A .δq q' c
        ... | fail = ⊥Ty↑-elim
        ... | ↑f q'' = id⊢

        stepP : (c : Alphabet)
          → ＂ c ＂ ⊗ ParseAlgCarrier *A ⟦_⟧P (↑f→q (*A .δq q' c))
          ⊢ D*.Trace true (↑q q')
        stepP c = D*.STEP c (↑q q') ∘⊢ (id⊢ ,⊗ relay c)

      pasteAt : Parse *A ⊢ D*.Trace true (↑q q)
      pasteAt = recParse *A pasteAlg initial

    ------------------------------------------------------------------
    -- One iteration of the body, as a continuation.

    ⟦_⟧M : FreelyAddInitial Q → TheoryTy _ tt
    ⟦ initial ⟧M = Parse *A ⟜ Parse *A
    ⟦ ↑i q ⟧M = D*.Trace true (↑q q) ⟜ Parse *A

    MAlg : ParseAlg M ⟦_⟧M
    MAlg fail = ParseAlgFail M
    MAlg initial =
      ⊕-elim (⊕ᴰ-elim stepM)
        (⊕ᴰ-elim λ p → Empty.rec (true≢false (Eq.eqToPath p ∙ notNullM)))
      ∘⊢ fromCode M true initial
      where
      conv : (c : Alphabet)
        → ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δᵢ c)) ⊗ Parse *A
        ⊢ D*.Trace true (↑f→q (M .δᵢ c))
      conv c with M .δᵢ c
      ... | fail = ⊥Ty-elim ∘⊢ ⊗⊥↑-annihL {A = Parse *A}
      ... | ↑f q'' = ⟜-app

      stepM : (c : Alphabet)
        → ＂ c ＂ ⊗ ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δᵢ c))
        ⊢ Parse *A ⟜ Parse *A
      stepM c =
        ⟜-intro (D*.STEP c initial ∘⊢ (id⊢ ,⊗ conv c) ∘⊢ ⊗-assoc)
    MAlg (↑q q) =
      ⊕-elim (⊕ᴰ-elim stepM) (⊕ᴰ-elim stopM)
      ∘⊢ fromCode M true (↑q q)
      where
      stopM : true Eq.≡ M .acc q → Lε ⊢ D*.Trace true (↑q q) ⟜ Parse *A
      stopM accEq =
        ⟜-intro (Paste.pasteAt q accEq ∘⊢ ⊗-unit-l ∘⊢ (lowerTy ,⊗ id⊢))

      stay : (c : Alphabet)
        → ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δq q c)) ⊗ Parse *A
        ⊢ D*.Trace true (↑f→q (M .δq q c))
      stay c with M .δq q c
      ... | fail = ⊥Ty-elim ∘⊢ ⊗⊥↑-annihL {A = Parse *A}
      ... | ↑f q'' = ⟜-app

      contra : (c : Alphabet)
        → ((q : Q) → M .acc q ≡ true → fail ≡ M .δq q c)
        → M .acc q Eq.≡ true
        → ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δq q c)) ⊗ Parse *A
        ⊢ D*.Trace true (↑f→q (M .δᵢ c))
      contra c h accEq with M .δq q c in dqEq
      ... | fail = ⊥Ty-elim ∘⊢ ⊗⊥↑-annihL {A = Parse *A}
      ... | ↑f q'' =
        Empty.rec
          (fail≢↑f
            (Eq.pathToEq (h q (Eq.eqToPath accEq) ∙ Eq.eqToPath dqEq)))

      conv : (c : Alphabet)
        → ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δq q c)) ⊗ Parse *A
        ⊢ D*.Trace true (↑f→q (*A .δq q c))
      conv c with M .acc q in accEq
      ... | false = stay c
      ... | true with seqUnambig c
      ...   | Sum.inr _ = stay c
      ...   | Sum.inl h = contra c h accEq

      stepM : (c : Alphabet)
        → ＂ c ＂ ⊗ ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δq q c))
        ⊢ D*.Trace true (↑q q) ⟜ Parse *A
      stepM c =
        ⟜-intro (D*.STEP c (↑q q) ∘⊢ (id⊢ ,⊗ conv c) ∘⊢ ⊗-assoc)

    ------------------------------------------------------------------
    -- ...and back: a run of the star is a list of runs of the body.

    ⟦_⟧* : FreelyAddInitial Q → TheoryTy _ tt
    ⟦ initial ⟧* = Parse M *
    ⟦ ↑i q ⟧* = DM.Trace true (↑q q) ⊗ (Parse M *)

    NILε : εTy ⊢ Parse M *
    NILε = NIL ∘⊢ liftTy

    *Alg : ParseAlg *A ⟦_⟧*
    *Alg fail = ParseAlgFail *A
    *Alg initial =
      ⊕-elim (⊕ᴰ-elim step*) (⊕ᴰ-elim λ _ → NILε ∘⊢ lowerTy)
      ∘⊢ fromCode *A true initial
      where
      helpInit : (c : Alphabet)
        → ParseAlgCarrier *A ⟦_⟧* (↑f→q (M .δᵢ c))
        ⊢ DM.Trace true (↑f→q (M .δᵢ c)) ⊗ (Parse M *)
      helpInit c with M .δᵢ c
      ... | fail = ⊥Ty↑-elim
      ... | ↑f q'' = id⊢

      step* : (c : Alphabet)
        → ＂ c ＂ ⊗ ParseAlgCarrier *A ⟦_⟧* (↑f→q (M .δᵢ c))
        ⊢ Parse M *
      step* c =
        CONS ∘⊢ (DM.STEP c initial ,⊗ id⊢) ∘⊢ ⊗-assoc⁻
        ∘⊢ (id⊢ ,⊗ helpInit c)
    *Alg (↑q q) =
      ⊕-elim (⊕ᴰ-elim step*) (⊕ᴰ-elim stop*)
      ∘⊢ fromCode *A true (↑q q)
      where
      stop* : true Eq.≡ M .acc q
        → Lε ⊢ DM.Trace true (↑q q) ⊗ (Parse M *)
      stop* accEq = (tA ,⊗ NILε) ∘⊢ ⊗ε-unit-l⁻ ∘⊢ lowerTy
        where
        tA : εTy ⊢ DM.Trace true (↑q q)
        tA = subst (λ v → εTy ⊢ DM.Trace v (↑q q))
               (sym (Eq.eqToPath accEq)) (DM.STOP (↑q q) ∘⊢ liftTy)

      helpStay : (c : Alphabet)
        → ParseAlgCarrier *A ⟦_⟧* (↑f→q (M .δq q c))
        ⊢ DM.Trace true (↑f→q (M .δq q c)) ⊗ (Parse M *)
      helpStay c with M .δq q c
      ... | fail = ⊥Ty↑-elim
      ... | ↑f q'' = id⊢

      stepStay : (c : Alphabet)
        → ＂ c ＂ ⊗ ParseAlgCarrier *A ⟦_⟧* (↑f→q (M .δq q c))
        ⊢ DM.Trace true (↑q q) ⊗ (Parse M *)
      stepStay c =
        (DM.STEP c (↑q q) ,⊗ id⊢) ∘⊢ ⊗-assoc⁻ ∘⊢ (id⊢ ,⊗ helpStay c)

      helpJump : (c : Alphabet)
        → ParseAlgCarrier *A ⟦_⟧* (↑f→q (M .δᵢ c))
        ⊢ DM.Trace true (↑f→q (M .δᵢ c)) ⊗ (Parse M *)
      helpJump c with M .δᵢ c
      ... | fail = ⊥Ty↑-elim
      ... | ↑f q'' = id⊢

      stepJump : (c : Alphabet) → M .acc q Eq.≡ true
        → ＂ c ＂ ⊗ ParseAlgCarrier *A ⟦_⟧* (↑f→q (M .δᵢ c))
        ⊢ DM.Trace true (↑q q) ⊗ (Parse M *)
      stepJump c accEq = (tA ,⊗ consR) ∘⊢ ⊗ε-unit-l⁻
        where
        tA : εTy ⊢ DM.Trace true (↑q q)
        tA = subst (λ v → εTy ⊢ DM.Trace v (↑q q))
               (Eq.eqToPath accEq) (DM.STOP (↑q q) ∘⊢ liftTy)

        consR : ＂ c ＂ ⊗ ParseAlgCarrier *A ⟦_⟧* (↑f→q (M .δᵢ c))
              ⊢ Parse M *
        consR =
          CONS ∘⊢ (DM.STEP c initial ,⊗ id⊢) ∘⊢ ⊗-assoc⁻
          ∘⊢ (id⊢ ,⊗ helpJump c)

      step* : (c : Alphabet)
        → ＂ c ＂ ⊗ ParseAlgCarrier *A ⟦_⟧* (↑f→q (*A .δq q c))
        ⊢ DM.Trace true (↑q q) ⊗ (Parse M *)
      step* c with M .acc q in accEq
      ... | false = stepStay c
      ... | true with seqUnambig c
      ...   | Sum.inr _ = stepStay c
      ...   | Sum.inl _ = stepJump c accEq

  *Aut→ : Parse *A ⊢ Parse M *
  *Aut→ = recParse *A *Alg initial

  *Aut← : Parse M * ⊢ Parse *A
  *Aut← = fold*r nilB consB
    where
    nilB : ⟦ starBranch (Parse M) false ⟧TheoryTy (λ _ → Parse *A)
         ⊢ Parse *A
    nilB = D*.STOP initial ∘⊢ star-nil⁻

    consB : ⟦ starBranch (Parse M) true ⟧TheoryTy (λ _ → Parse *A)
          ⊢ Parse *A
    consB =
      ⟜-app ∘⊢ (recParse M MAlg initial ,⊗ id⊢) ∘⊢ star-cons⁻

------------------------------------------------------------------------
-- `unambiguous⊗`: the old `unambig-M⊗M'`, over the same hypothesis the
-- star lemma uses.  `Precise.splitAgree` does the combinatorics: the two
-- cuts coincide, so the factors are equal by their own unambiguity.

unambiguous⊗ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → ((c : Alphabet) → (c ∉FollowLast A) Sum.⊎ (c ∉First B))
  → unambiguous A → unambiguous B → unambiguous (A ⊗ B)
unambiguous⊗ {A = A} {B = B} su uA uB m
  (ms , e , (a , (b , _))) (ns , f , (a' , (b' , _))) =
  ⊗PathP' refl sp
    (isPropPathP _ (uA (ms zero)) a a')
    (isPropPathP _ (uB (ms (suc zero))) b b')
  where
  pieces : (ms zero ≡ ns zero) × (ms (suc zero) ≡ ns (suc zero))
  pieces =
    splitAgree su su (ms zero) (ms (suc zero)) (ns zero) (ns (suc zero))
      (Eq.eqToPath e ∙ sym (Eq.eqToPath f)) a b a' b'

  sp : ms ≡ ns
  sp = funExt λ where
    zero → pieces .fst
    (suc zero) → pieces .snd

-- ...and the two easy companions.

unambiguous⊕ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → unambiguous A → unambiguous B → (A & B ⊢ ⊥Ty) → unambiguous (A ⊕ B)
unambiguous⊕ uA uB dis m (Sum.inl x) (Sum.inl y) = cong Sum.inl (uA m x y)
unambiguous⊕ uA uB dis m (Sum.inl x) (Sum.inr y) =
  Empty.rec (dis m (x , y) .lower)
unambiguous⊕ uA uB dis m (Sum.inr x) (Sum.inl y) =
  Empty.rec (dis m (y , x) .lower)
unambiguous⊕ uA uB dis m (Sum.inr x) (Sum.inr y) = cong Sum.inr (uB m x y)

-- disjoint firsts and not both nullable is disjointness -- that is
-- `SequentialUnambiguity.First`'s `#→disjoint`, and `_#_` unfolds to
-- exactly this hypothesis.
disjointFirsts→ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → ((c : Alphabet) → (c ∉First A) Sum.⊎ (c ∉First B))
  → (¬Nullable A) Sum.⊎ (¬Nullable B)
  → A & B ⊢ ⊥Ty
disjointFirsts→ = #→disjoint

unambiguous-satG : (P : Alphabet → Bool) → unambiguous (satG P)
unambiguous-satG P m (x , p) (y , q) =
  ΣPathP (xy , isProp→PathP (λ _ → isPropEqString) p q)
  where
  xy : x ≡ y
  xy = Σ≡Prop (λ _ → isSetBool _ _)
         (L.cons-inj₁ (sym (Eq.eqToPath p) ∙ Eq.eqToPath q))

-- functoriality of the star, as a fold
map* : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} → A ⊢ B → A * ⊢ B *
map* {A = A} {B = B} f =
  fold*r (NIL ∘⊢ liftTy ∘⊢ lowerTy ∘⊢ star-nil⁻ {A = A} {B = B *})
         (CONS ∘⊢ (f ,⊗ id⊢) ∘⊢ star-cons⁻)

------------------------------------------------------------------------
-- The three side conditions `compile` builds, replayed.  `Compile` keeps
-- them private, and the compiled automaton is only *definitionally* the
-- one these produce, so they have to be written again here.

private
  notBoth' : {N N' : Bool} → b or b' Eq.≡ true
    → N ≡ not b → N' ≡ not b' → (N ≡ false) Sum.⊎ (N' ≡ false)
  notBoth' {b = true} _ p _ = Sum.inl p
  notBoth' {b = false} {b' = true} _ _ q = Sum.inr q
  notBoth' {b = false} {b' = false} () _ _

  seqOf' : {¬FL ¬FL' ¬F ¬F' : ℙ}
    (dr : DetReg ¬FL ¬F b) (dr' : DetReg ¬FL' ¬F' b')
    → ((c : Alphabet) → (c ∈ℙ ¬FL) Sum.⊎ (c ∈ℙ ¬F'))
    → (c : Alphabet)
    → ((q : States dr) → Aut dr .acc q ≡ true → fail ≡ Aut dr .δq q c)
      Sum.⊎ (fail ≡ Aut dr' .δᵢ c)
  seqOf' dr dr' su c =
    Sum.map (δq-fail disc dr c) (δᵢ-fail disc dr' c) (su c)

  firstsOf' : {¬FL ¬FL' ¬F ¬F' : ℙ}
    (dr : DetReg ¬FL ¬F b) (dr' : DetReg ¬FL' ¬F' b')
    → ((c : Alphabet) → (c ∈ℙ ¬F) Sum.⊎ (c ∈ℙ ¬F'))
    → (c : Alphabet)
    → (fail ≡ Aut dr .δᵢ c) Sum.⊎ (fail ≡ Aut dr' .δᵢ c)
  firstsOf' dr dr' sep c =
    Sum.map (δᵢ-fail disc dr c) (δᵢ-fail disc dr' c) (sep c)

------------------------------------------------------------------------
-- The two maps, by induction on the deterministic regular expression.

fromAut : {¬FL ¬F : ℙ} (dr : DetReg ¬FL ¬F b)
  → Parse (Aut dr) ⊢ ty ⟦ erase dr ⟧
toAut : {¬FL ¬F : ℙ} (dr : DetReg ¬FL ¬F b)
  → ty ⟦ erase dr ⟧ ⊢ Parse (Aut dr)

fromAut εdr = Leaves.εAut→
fromAut ⊥dr = Leaves.⊥Aut→
fromAut ＂ c ＂dr = Leaves.litAut→ c
fromAut (satdr P) = Leaves.satAut→ P
fromAut (dr ⊗DR[ su ] dr') =
  (fromAut dr ,⊗ fromAut dr')
  ∘⊢ Seq.⊗Aut→ (Aut dr) (Aut dr') (nullOf disc dr) (seqOf' dr dr' su)
fromAut (_⊕DR[_]_ {b = true} {notBothNull = nbn} dr sep dr') =
  ⊕-elim (inl ∘⊢ fromAut dr) (inr ∘⊢ fromAut dr')
  ∘⊢ Alt.⊕Aut→ (Aut dr) (Aut dr')
      (notBoth' nbn (nullOf disc dr) (nullOf disc dr'))
      (firstsOf' dr dr' sep)
fromAut (_⊕DR[_]_ {b = false} {b' = true} {notBothNull = nbn} dr sep dr') =
  ⊕-elim (inl ∘⊢ fromAut dr) (inr ∘⊢ fromAut dr')
  ∘⊢ Alt.⊕Aut→ (Aut dr) (Aut dr')
      (notBoth' nbn (nullOf disc dr) (nullOf disc dr'))
      (firstsOf' dr dr' sep)
fromAut (_⊕DR[_]_ {b = false} {b' = false} {notBothNull = ()} dr sep dr')
fromAut (dr *DR[ su ]) =
  map* (fromAut dr)
  ∘⊢ Kleene.*Aut→ (Aut dr) (nullOf disc dr) (seqOf' dr dr su)

toAut εdr = Leaves.εAut←
toAut ⊥dr = Leaves.⊥Aut←
toAut ＂ c ＂dr = Leaves.litAut← c
toAut (satdr P) = Leaves.satAut← P
toAut (dr ⊗DR[ su ] dr') =
  Seq.⊗Aut← (Aut dr) (Aut dr') (nullOf disc dr) (seqOf' dr dr' su)
  ∘⊢ (toAut dr ,⊗ toAut dr')
toAut (_⊕DR[_]_ {b = true} {notBothNull = nbn} dr sep dr') =
  Alt.⊕Aut← (Aut dr) (Aut dr')
    (notBoth' nbn (nullOf disc dr) (nullOf disc dr'))
    (firstsOf' dr dr' sep)
  ∘⊢ ⊕-elim (inl ∘⊢ toAut dr) (inr ∘⊢ toAut dr')
toAut (_⊕DR[_]_ {b = false} {b' = true} {notBothNull = nbn} dr sep dr') =
  Alt.⊕Aut← (Aut dr) (Aut dr')
    (notBoth' nbn (nullOf disc dr) (nullOf disc dr'))
    (firstsOf' dr dr' sep)
  ∘⊢ ⊕-elim (inl ∘⊢ toAut dr) (inr ∘⊢ toAut dr')
toAut (_⊕DR[_]_ {b = false} {b' = false} {notBothNull = ()} dr sep dr')
toAut (dr *DR[ su ]) =
  Kleene.*Aut← (Aut dr) (nullOf disc dr) (seqOf' dr dr su)
  ∘⊢ map* (toAut dr)

------------------------------------------------------------------------
-- Unambiguity of the denotation, by the same induction.  The letter-set
-- side conditions travel from the automaton through `toAut`; the two
-- combinatorial lemmas are `unambiguous⊗` and `unambiguous-*`.

private
  ¬NullOf : {¬FL ¬F : ℙ} (dr : DetReg ¬FL ¬F true)
    → ¬Nullable (ty ⟦ erase dr ⟧)
  ¬NullOf dr =
    ¬NullableAut (Aut dr) (nullOf disc dr) ∘⊢ &-swap
    ∘⊢ (toAut dr ,&p id⊢)

  seqOfTy : {¬FL ¬FL' ¬F ¬F' : ℙ}
    (dr : DetReg ¬FL ¬F true) (dr' : DetReg ¬FL' ¬F' b')
    → ((c : Alphabet) → (c ∈ℙ ¬FL) Sum.⊎ (c ∈ℙ ¬F'))
    → (c : Alphabet)
    → (c ∉FollowLast (ty ⟦ erase dr ⟧)) Sum.⊎ (c ∉First (ty ⟦ erase dr' ⟧))
  seqOfTy dr dr' su c with su c
  ... | Sum.inl h =
    Sum.inl
      (¬FollowLastAut (Aut dr) c (nullOf disc dr) (δq-fail disc dr c h)
       ∘⊢ ((toAut dr ,⊗ id⊢) ,&p toAut dr))
  ... | Sum.inr h =
    Sum.inr
      (¬FirstAut (Aut dr') c (δᵢ-fail disc dr' c h)
       ∘⊢ (id⊢ ,&p toAut dr'))

  firstOfTy : {¬FL ¬FL' ¬F ¬F' : ℙ}
    (dr : DetReg ¬FL ¬F b) (dr' : DetReg ¬FL' ¬F' b')
    → ((c : Alphabet) → (c ∈ℙ ¬F) Sum.⊎ (c ∈ℙ ¬F'))
    → (c : Alphabet)
    → (c ∉First (ty ⟦ erase dr ⟧)) Sum.⊎ (c ∉First (ty ⟦ erase dr' ⟧))
  firstOfTy dr dr' sep c =
    Sum.map
      (λ h → ¬FirstAut (Aut dr) c (δᵢ-fail disc dr c h)
             ∘⊢ (id⊢ ,&p toAut dr))
      (λ h → ¬FirstAut (Aut dr') c (δᵢ-fail disc dr' c h)
             ∘⊢ (id⊢ ,&p toAut dr'))
      (sep c)

unambig-erase : {¬FL ¬F : ℙ} (dr : DetReg ¬FL ¬F b)
  → unambiguous (ty ⟦ erase dr ⟧)
unambig-erase εdr = isPropεTy
unambig-erase ⊥dr = unambiguous⊥
unambig-erase ＂ c ＂dr = λ _ → isPropEqString
unambig-erase (satdr P) = unambiguous-satG P
unambig-erase (dr ⊗DR[ su ] dr') =
  unambiguous⊗ (seqOfTy dr dr' su) (unambig-erase dr) (unambig-erase dr')
unambig-erase (_⊕DR[_]_ {b = true} {notBothNull = nbn} dr sep dr') =
  unambiguous⊕ (unambig-erase dr) (unambig-erase dr')
    (disjointFirsts→ (firstOfTy dr dr' sep) (Sum.inl (¬NullOf dr)))
unambig-erase (_⊕DR[_]_ {b = false} {b' = true} {notBothNull = nbn} dr sep dr') =
  unambiguous⊕ (unambig-erase dr) (unambig-erase dr')
    (disjointFirsts→ (firstOfTy dr dr' sep) (Sum.inr (¬NullOf dr')))
unambig-erase (_⊕DR[_]_ {b = false} {b' = false} {notBothNull = ()} dr sep dr')
unambig-erase (dr *DR[ su ]) =
  unambiguous-* (¬NullOf dr) (seqOfTy dr dr su) (unambig-erase dr)

------------------------------------------------------------------------
-- The theorem.

compile-sound : {¬FL ¬F : ℙ} (dr : DetReg ¬FL ¬F b)
  → Parse (compile disc dr) ≅ ty ⟦ erase dr ⟧
compile-sound dr =
  ≈→≅
    (unambiguousTrace (IDA→DA (Aut dr)) true initial)
    (unambig-erase dr)
    (fromAut dr)
    (toAut dr)
