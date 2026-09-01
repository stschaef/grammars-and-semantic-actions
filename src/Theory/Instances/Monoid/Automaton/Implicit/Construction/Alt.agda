{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- ported from `Automata/Implicit/RegExp/WeakEquivalences`'s `⊕Aut≈`;
   no lifting since every state set here sits at `ℓAlph` -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Automaton.Implicit.Construction.Alt
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

module Alt {Q Q' : Type ℓAlph}
  (M : ImplicitDeterministicAutomaton Q)
  (M' : ImplicitDeterministicAutomaton Q')
  (notBothNull : (M .null ≡ false) Sum.⊎ (M' .null ≡ false))
  (disjointFirsts :
    (c : Alphabet) → (fail ≡ M .δᵢ c) Sum.⊎ (fail ≡ M' .δᵢ c))
  where

  ⊕A : ImplicitDeterministicAutomaton (Q Sum.⊎ Q')
  ⊕A = ⊕Aut discAlphabet M M' notBothNull disjointFirsts

  private
    module DM = DeterministicAutomaton (IDA→DA M)
    module DM' = DeterministicAutomaton (IDA→DA M')
    module D⊕ = DeterministicAutomaton (IDA→DA ⊕A)

    Lε : TheoryTy (ℓF ℓM) tt
    Lε = LiftTheoryTy (ℓF ℓM) εTy

    ⟦_⟧M : FreelyAddInitial Q → TheoryTy _ tt
    ⟦ initial ⟧M = Parse ⊕A
    ⟦ ↑i q ⟧M = D⊕.Trace true (↑q (Sum.inl q))

    ⟦_⟧M' : FreelyAddInitial Q' → TheoryTy _ tt
    ⟦ initial ⟧M' = Parse ⊕A
    ⟦ ↑i q' ⟧M' = D⊕.Trace true (↑q (Sum.inr q'))

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

