{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `Paste` is what `KL*` needs and `⊗` does not: a further `Parse *A`
   re-entered at an accepting state of the body -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Automaton.Implicit.Construction.Kleene
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

module Kleene {Q : Type ℓAlph}
  (M : ImplicitDeterministicAutomaton Q)
  (notNullM : M .null ≡ false)
  (seqUnambig :
    (c : Alphabet)
    → ((q : Q) → M .acc q ≡ true → fail ≡ M .δq q c)
      Sum.⊎ (fail ≡ M .δᵢ c))
  where

  *A : ImplicitDeterministicAutomaton Q
  *A = *Aut discAlphabet M notNullM seqUnambig

  private
    module DM = DeterministicAutomaton (IDA→DA M)
    module D* = DeterministicAutomaton (IDA→DA *A)

    Lε : TheoryTy (ℓF ℓM) tt
    Lε = LiftTheoryTy (ℓF ℓM) εTy

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
    nilB = D*.STOP initial ∘⊢ liftTy ∘⊢ NIL-elim {A = Parse M}

    consB : ⟦ starBranch (Parse M) true ⟧TheoryTy (λ _ → Parse *A)
          ⊢ Parse *A
    consB =
      ⟜-app ∘⊢ (recParse M MAlg initial ,⊗ id⊢) ∘⊢ UNCONS-branch
