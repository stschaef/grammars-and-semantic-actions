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

open import Cubical.Data.Bool using (Bool ; true ; false ; not ; _or_ ; isSetBool)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.List.Properties as L
open import Cubical.Data.Sigma
  using (Σ-syntax ; _×_ ; _,_ ; fst ; snd ; ΣPathP ; Σ≡Prop)
open import Cubical.Relation.Nullary.Base using (Discrete)
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
open import Theory.Instances.Monoid.SequentialUnambiguity.Base
  Alphabet isSetAlphabet
  using (#→disjoint ; unambiguous⊗ ; unambiguous⊕)
open import Theory.Instances.Monoid.Automaton.Implicit.Analysis
  Alphabet _≟_ ℓ public
open import Theory.Instances.Monoid.Automaton.Deterministic
  Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Implicit.Disjointness
  Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Unambiguous
  Alphabet isSetAlphabet
  using (unambiguousTrace)
open import Theory.Instances.Monoid.Unitor Alphabet isSetAlphabet
  using (isPropεTy)
open import Theory.Instances.Monoid.Regex.Base Alphabet _≟_ ℓ using (⟦_⟧ ; satG)

open WildCatNotation
open WildCatIso
open ImplicitDeterministicAutomaton

private variable
  ℓA ℓB ℓX : Level
  b b' : Bool

-- Two maps plus unambiguity of both ends is an iso.

open import Theory.Type.Unambiguity.Disjoint MonEqns Alphabet (λ _ → tt)
  listPresentation using () renaming (unambiguous→≅ to ≈→≅)

disc : Discrete Alphabet
disc = discAlphabet

Aut : {¬FL ¬F : ℙ} (dr : DetReg ¬FL ¬F b)
  → ImplicitDeterministicAutomaton (States dr)
Aut dr = compile disc dr

open import Theory.Instances.Monoid.Automaton.Implicit.Construction.Leaves
  Alphabet _≟_ ℓ public
open import Theory.Instances.Monoid.Automaton.Implicit.Construction.Alt
  Alphabet _≟_ ℓ public
open import Theory.Instances.Monoid.Automaton.Implicit.Construction.Seq
  Alphabet _≟_ ℓ public
open import Theory.Instances.Monoid.Automaton.Implicit.Construction.Kleene
  Alphabet _≟_ ℓ public

open import Theory.Instances.Monoid.KleeneStar.Map Alphabet isSetAlphabet
  renaming (*-map to map*)

unambiguous-satG : (P : Alphabet → Bool) → unambiguous (satG P)
unambiguous-satG P m (x , p) (y , q) =
  ΣPathP (xy , isProp→PathP (λ _ → isPropEqString) p q)
  where
  xy : x ≡ y
  xy = Σ≡Prop (λ _ → isSetBool _ _)
         (L.cons-inj₁ (sym (Eq.eqToPath p) ∙ Eq.eqToPath q))

-- `compile`'s three side conditions, replayed: `Compile` keeps them
-- private and the automaton is only definitionally the one they produce

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

-- letter-set side conditions travel through `toAut`; the combinatorial
-- lemmas are `unambiguous⊗` and `unambiguous-*`

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
    (#→disjoint (firstOfTy dr dr' sep) (Sum.inl (¬NullOf dr)))
unambig-erase (_⊕DR[_]_ {b = false} {b' = true} {notBothNull = nbn} dr sep dr') =
  unambiguous⊕ (unambig-erase dr) (unambig-erase dr')
    (#→disjoint (firstOfTy dr dr' sep) (Sum.inr (¬NullOf dr')))
unambig-erase (_⊕DR[_]_ {b = false} {b' = false} {notBothNull = ()} dr sep dr')
unambig-erase (dr *DR[ su ]) =
  unambiguous-* (¬NullOf dr) (seqOfTy dr dr su) (unambig-erase dr)

compile-sound : {¬FL ¬F : ℙ} (dr : DetReg ¬FL ¬F b)
  → Parse (compile disc dr) ≅ ty ⟦ erase dr ⟧
compile-sound dr =
  ≈→≅
    (unambiguousTrace (IDA→DA (Aut dr)) true initial)
    (unambig-erase dr)
    (fromAut dr)
    (toAut dr)
