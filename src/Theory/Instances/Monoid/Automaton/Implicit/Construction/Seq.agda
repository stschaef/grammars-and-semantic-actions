{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- left factor's trace in continuation style (`- ⟜ Parse M'`): the right
   factor splices in exactly where the left accepts -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Automaton.Implicit.Construction.Seq
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
  ⊗A = ⊗Aut discAlphabet M M' notNullM seqUnambig

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

