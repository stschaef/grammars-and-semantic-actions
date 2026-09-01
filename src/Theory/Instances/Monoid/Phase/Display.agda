{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Instance-resolved pretty-printer: `shown` is a `SemanticAction A String`. -}
open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.Phase.Display where

open import Cubical.Data.Unit using (Unit ; tt ; Unit* ; tt*)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.FinData using (zero ; suc)
import Cubical.Data.List as L
open L using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Bool using (Bool ; true ; false)
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
import Cubical.Data.Maybe as Mb
import Cubical.Data.Equality as Eq
import Agda.Builtin.String as AS

import Theory.Type.Decidable.Base as DecBase
import Theory.Instances.Monoid.Base as MB
import Theory.Instances.Monoid.Strings as Str
import Theory.Instances.Monoid.KleeneStar as KS
import Theory.Instances.Monoid.SemanticAction as SA
import Theory.Instances.Monoid.Phase as Ph
import Theory.Instances.Monoid.Regex.Sat as RSat
import Theory.Instances.Monoid.Regex.Unicode as RU

module Displays
  {ℓAlph} (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet)
  (showA : Alphabet → AS.String) where

  -- Only `Phase`'s names re-exported; the formers would be ambiguous at use sites.
  open Str Alphabet isSetAlphabet hiding (Δ)
  open KS Alphabet isSetAlphabet
  open SA Alphabet isSetAlphabet
  open Ph Alphabet isSetAlphabet public

  module Dec = DecBase MB.MonEqns Alphabet (λ _ → tt) listPresentation

  private variable ℓA ℓB ℓX ℓY : Level

  cat : List AS.String → AS.String
  cat [] = ""
  cat (s ∷ ss) = AS.primStringAppend s (cat ss)

  showAll : List Alphabet → AS.String
  showAll cs = cat (L.map showA cs)

  mkDisplay : {A : TheoryTy ℓA tt} → SemanticAction A AS.String → Display A
  mkDisplay a = record { shown = a }

  instance
    Display-εTy : Display εTy
    Display-εTy = mkDisplay (semact-pure "")

    Display-lit : {c : Alphabet} → Display ＂ c ＂
    Display-lit {c} = mkDisplay (semact-pure (showA c))

    Display-char : Display char
    Display-char = mkDisplay (semact-map showA semact-char)

    Display-⊗ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
      → {{Display A}} → {{Display B}} → Display (A ⊗ B)
    Display-⊗ {{da}} {{db}} = mkDisplay
      (semact-map (λ p → AS.primStringAppend (p .fst) (p .snd))
        (semact-⊗₂ (Display.shown da) (Display.shown db)))

    Display-⊕ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
      → {{Display A}} → {{Display B}} → Display (A ⊕ B)
    Display-⊕ {{da}} {{db}} =
      mkDisplay (semact-⊕ (Display.shown da) (Display.shown db))

    Display-* : {A : TheoryTy ℓA tt} → {{Display A}} → Display (A *)
    Display-* {{da}} =
      mkDisplay (semact-map cat (semact-* (Display.shown da)))

    -- `⊤Ty`'s *index* is the whole word; `read` exposes it as a parse.
    Display-⊤Ty : Display ⊤Ty
    Display-⊤Ty = mkDisplay
      (semact-map showAll (semact-map-g read semact-String*))

    Display-⊥Ty : Display ⊥Ty
    Display-⊥Ty = mkDisplay semact-⊥

    Display-Lift : {A : TheoryTy ℓA tt} → {{Display A}}
      → Display (LiftTheoryTy ℓB A)
    Display-Lift {{da}} = mkDisplay (semact-lift (Display.shown da))

    -- `Display-*` does not fire on `String*` (distinct codes); every
    -- hand-written `μ` needs its own instance.
    Display-String* : Display String*
    Display-String* = mkDisplay (semact-map showAll semact-String*)

  -- NOT an instance: every ⊕ᴰ-defined grammar would get two candidates
  -- (measured: it makes even `Display char` resolution stick).

  displayΣ : {Y : Type ℓY} {A : Y → TheoryTy ℓA tt}
    → ((y : Y) → Display (A y)) → Display (⊕[ y ∈ Y ] A y)
  displayΣ ds = mkDisplay (semact-⊕ᴰ' (λ y → Display.shown (ds y)))

  displayΣ-tagged : {Y : Type ℓY} {A : Y → TheoryTy ℓA tt}
    → (Y → AS.String) → ((y : Y) → Display (A y))
    → Display (⊕[ y ∈ Y ] A y)
  displayΣ-tagged showY ds = mkDisplay (semact-⊕ᴰ' λ y →
    semact-map (AS.primStringAppend (showY y)) (Display.shown (ds y)))

  theDisplay : {A : TheoryTy ℓA tt} → {{Display A}} → Display A
  theDisplay {{d}} = d

  display : {A : TheoryTy ℓA tt} → {{Display A}} → (w : String) → A w
    → AS.String
  display {{d}} w p = Display.shown d w p .fst

  displayDec : {A : TheoryTy ℓA tt} → {{Display A}}
    → Dec.Decidable A → String → Mb.Maybe AS.String
  displayDec {{d}} dc = observe dc (semact-dec (Display.shown d))

-- `satG P`'s ⊕ᴰ index *is* renderable, so it gets a bespoke instance;
-- with it `ty ⟦ r ⟧` resolves for every regex `r`.

module SatDisplay
  {ℓAlph} (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level) (showA : Alphabet → AS.String) where

  open RSat Alphabet _≟_ ℓ using (Sat ; satG ; isSetAlphabet)
  open SA Alphabet isSetAlphabet using (SemanticAction ; semact-⊕ᴰ' ; semact-pure)

  open Displays Alphabet isSetAlphabet showA public

  instance
    Display-satG : {P : Alphabet → Bool} → Display (satG P)
    Display-satG =
      mkDisplay (semact-⊕ᴰ' λ x → semact-pure (showA (x .fst)))
