{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The canonical pretty-printer, as an instance-resolved semantic action.

   `Phase.Display` says a grammar knows how to print itself: `shown` is a
   `SemanticAction A String`, so a test prints a parse by *running the
   grammar's own action* rather than by projecting out of the parse.  This
   file supplies the instances for the connectives, so that a display for
   `＂ a ＂ ⊗ (＂ b ＂ ⊕ ＂ c ＂) ⊗ ＂ d ＂ *` is assembled by resolution.

   Rendering an `Alphabet` is a parameter, not an assumption: nothing here
   knows about Unicode. -}
open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.Phase.Display where

open import Cubical.Data.Unit using (Unit ; tt ; Unit*)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.FinData using (zero ; suc)
import Cubical.Data.List as L
open L using (List ; [] ; _∷_)
open import Cubical.Data.Bool using (Bool)
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

module Displays
  {ℓAlph} (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet)
  (showA : Alphabet → AS.String) where

  -- Only `Phase`'s own names are re-exported.  The grammar formers and the
  -- action combinators are *not*: a client of this module has them from
  -- its own `Strings`/`SemanticAction` opening already, and re-exporting
  -- them here makes every such name ambiguous at the use site.
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

    -- `⊤Ty` holds no information, but its *index* is the whole word, and
    -- `read` is the internal map that exposes it as a parse.  So this is
    -- still an action, not a peek at the index.
    Display-⊤Ty : Display ⊤Ty
    Display-⊤Ty = mkDisplay
      (semact-map showAll (semact-map-g read semact-String*))

    Display-⊥Ty : Display ⊥Ty
    Display-⊥Ty = mkDisplay semact-⊥

    Display-Lift : {A : TheoryTy ℓA tt} → {{Display A}}
      → Display (LiftTheoryTy ℓB A)
    Display-Lift {{da}} = mkDisplay (semact-lift (Display.shown da))

    -- `String*` is a `μ`, and `Display-*` does *not* fire on it: the two
    -- codes (`KleeneCode` vs `StarCode char`) are deliberately distinct
    -- definitions, so it needs its own instance.  The same holds for every
    -- other hand-written `μ` -- `Examples.Dyck`, `Grammars.Dyck`, the NFA
    -- `Trace` -- none of which resolves without one.
    Display-String* : Display String*
    Display-String* = mkDisplay (semact-map showAll semact-String*)

  -- The dependent sum, deliberately not an instance.  Two reasons, both
  -- real:
  --
  --  * `⊕[ y ∈ Y ] A y` has nothing renderable in it unless `Y` does, so
  --    the honest signature takes a `Y → String` as well;
  --  * every grammar in this development that is *defined* as a `⊕ᴰ` --
  --    `char`, `Δ X`, `satTy P`, every `⟦ ⊕e ... ⟧` layer -- would then
  --    have two candidate instances.  Measured: adding it makes even
  --    `Display char` report `Candidates Display-⊕ᴰ, Display-⊗ (stuck)`.
  --    Pass it explicitly instead.

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

-- `satTy P` -- a letter satisfying `P` -- is a `⊕ᴰ` over `Sat P`, so it is
-- exactly the case the generic `⊕ᴰ` instance was refused for.  Here the
-- index *is* renderable (its first component is a letter), so it gets a
-- bespoke instance.  With it, `ty ⟦ r ⟧` resolves for every regex `r`:
-- `ty` of `⊗Set`/`⊕Set`/`StarSet`/`litSet`/`εSet`/`⊥Set` all reduce to
-- the connectives above.

module SatDisplay
  {ℓAlph} (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level) (showA : Alphabet → AS.String) where

  open RSat Alphabet _≟_ ℓ using (Sat ; satTy ; isSetAlphabet)
  open SA Alphabet isSetAlphabet using (SemanticAction ; semact-⊕ᴰ' ; semact-pure)

  open Displays Alphabet isSetAlphabet showA public

  instance
    Display-satTy : {P : Alphabet → Bool} → Display (satTy P)
    Display-satTy =
      mkDisplay (semact-⊕ᴰ' λ x → semact-pure (showA (x .fst)))
