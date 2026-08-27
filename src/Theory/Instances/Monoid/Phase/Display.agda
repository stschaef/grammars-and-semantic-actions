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

------------------------------------------------------------------------
-- The instances.

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

  -- `AS.String` is a monoid too; this is its fold.
  cat : List AS.String → AS.String
  cat [] = ""
  cat (s ∷ ss) = AS.primStringAppend s (cat ss)

  showAll : List Alphabet → AS.String
  showAll cs = cat (L.map showA cs)

  mkDisplay : {A : TheoryTy ℓA tt} → SemanticAction A AS.String → Display A
  mkDisplay a = record { shown = a }

  instance
    -- ε prints as nothing at all.
    Display-εTy : Display εTy
    Display-εTy = mkDisplay (semact-pure "")

    -- a literal prints as its own letter; the index is known statically
    Display-lit : {c : Alphabet} → Display ＂ c ＂
    Display-lit {c} = mkDisplay (semact-pure (showA c))

    -- ...and `char` reads the letter the parse selected
    Display-char : Display char
    Display-char = mkDisplay (semact-map showA semact-char)

    -- concatenation, at the splitting the tensor already carries
    Display-⊗ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
      → {{Display A}} → {{Display B}} → Display (A ⊗ B)
    Display-⊗ {{da}} {{db}} = mkDisplay
      (semact-map (λ p → AS.primStringAppend (p .fst) (p .snd))
        (semact-⊗₂ (Display.shown da) (Display.shown db)))

    -- whichever side of the sum the parse is on
    Display-⊕ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
      → {{Display A}} → {{Display B}} → Display (A ⊕ B)
    Display-⊕ {{da}} {{db}} =
      mkDisplay (semact-⊕ (Display.shown da) (Display.shown db))

    -- the star is the fold of the pieces, in order
    Display-* : {A : TheoryTy ℓA tt} → {{Display A}} → Display (A *)
    Display-* {{da}} =
      mkDisplay (semact-map cat (semact-* (Display.shown da)))

    -- `⊤Ty` holds no information, but its *index* is the whole word, and
    -- `read` is the internal map that exposes it as a parse.  So this is
    -- still an action, not a peek at the index.
    Display-⊤Ty : Display ⊤Ty
    Display-⊤Ty = mkDisplay
      (semact-map showAll (semact-map-g read semact-String*))

    -- nothing to print, vacuously
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

  ----------------------------------------------------------------------
  -- The dependent sum.
  --
  -- NOT an instance.  Two reasons, both real:
  --
  --  * `⊕[ y ∈ Y ] A y` has nothing renderable in it unless `Y` does, so
  --    the honest signature takes a `Y → String` as well;
  --  * every grammar in this development that is *defined* as a `⊕ᴰ` --
  --    `char`, `Δ X`, `satG P`, every `⟦ ⊕e ... ⟧` layer -- would then
  --    have two candidate instances.  Measured: adding it makes even
  --    `Display char` report `Candidates Display-⊕ᴰ, Display-⊗ (stuck)`.
  --    Pass it explicitly instead.

  displayΣ : {Y : Type ℓY} {A : Y → TheoryTy ℓA tt}
    → ((y : Y) → Display (A y)) → Display (⊕[ y ∈ Y ] A y)
  displayΣ ds = mkDisplay (semact-⊕ᴰ' (λ y → Display.shown (ds y)))

  -- ...and the tagged version, when the index can be named.
  displayΣ-tagged : {Y : Type ℓY} {A : Y → TheoryTy ℓA tt}
    → (Y → AS.String) → ((y : Y) → Display (A y))
    → Display (⊕[ y ∈ Y ] A y)
  displayΣ-tagged showY ds = mkDisplay (semact-⊕ᴰ' λ y →
    semact-map (AS.primStringAppend (showY y)) (Display.shown (ds y)))

  ----------------------------------------------------------------------
  -- The boundary: a parse, printed.

  -- the resolved record itself, for the places that need to hand it on
  theDisplay : {A : TheoryTy ℓA tt} → {{Display A}} → Display A
  theDisplay {{d}} = d

  display : {A : TheoryTy ℓA tt} → {{Display A}} → (w : String) → A w
    → AS.String
  display {{d}} w p = Display.shown d w p .fst

  -- ...and the same for a decision, so a test can print the refutation
  -- branch as `nothing` instead of dropping it.  This is `runPhase` with
  -- the emission replaced by the canonical one.
  displayDec : {A : TheoryTy ℓA tt} → {{Display A}}
    → Dec.Decidable A → String → Mb.Maybe AS.String
  displayDec {{d}} dc = observe dc (semact-dec (Display.shown d))

------------------------------------------------------------------------
-- One more former, from the regex layer.
--
-- `satG P` -- a letter satisfying `P` -- is a `⊕ᴰ` over `Sat P`, so it is
-- exactly the case the generic `⊕ᴰ` instance was refused for.  Here the
-- index *is* renderable (its first component is a letter), so it gets a
-- bespoke instance.  With it, `ty ⟦ r ⟧` resolves for every regex `r`:
-- `ty` of `⊗Set`/`⊕Set`/`StarSet`/`litSet`/`εSet`/`⊥Set` all reduce to
-- the connectives above.

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

------------------------------------------------------------------------
-- Demo.

module Demo where

  open import Theory.Instances.Monoid.Unicode.Base
    using (UChar ; isSetUChar ; ch ; untext ; text)

  showU : UChar → AS.String
  showU c = untext (c ∷ [])

  open Str UChar isSetUChar hiding (Δ)
  open KS UChar isSetUChar
  open SA UChar isSetUChar
  open Displays UChar isSetUChar showU

  a b c d : UChar
  a = ch 'a'
  b = ch 'b'
  c = ch 'c'
  d = ch 'd'

  -- Introduction rules, as points.  `op _⊙_ (two x y)` reduces to `x ++ y`
  -- on this presentation, so the index equation is `Eq.refl`.
  lit-pt : (x : UChar) → ＂ x ＂ (x ∷ [])
  lit-pt x = Eq.refl

  -- Both grammars are explicit: `(A ⊗ B) (x ++ y)` puts `A` and `B` under
  -- an application, so leaving them implicit blocks pattern unification.
  ⊗pt : {ℓA ℓB : Level} (A : TheoryTy ℓA tt) (B : TheoryTy ℓB tt)
    (x y : String) → A x → B y → (A ⊗ B) (x ++ y)
  ⊗pt A B x y p q = MB.two x y , Eq.refl , (p , (q , tt*))

  -- `a (b|c) d*`
  Alt Ds Tail G : TheoryTy _ tt
  Alt = ＂ b ＂ ⊕ ＂ c ＂
  Ds = ＂ d ＂ *
  Tail = Alt ⊗ Ds
  G = ＂ a ＂ ⊗ Tail

  nilD : Ds []
  nilD = NIL {A = ＂ d ＂} [] (lift εTy-pt)

  ds : Ds (d ∷ d ∷ [])
  ds = CONS {A = ＂ d ＂} _
         (⊗pt ＂ d ＂ Ds (d ∷ []) (d ∷ []) (lit-pt d)
           (CONS {A = ＂ d ＂} _
             (⊗pt ＂ d ＂ Ds (d ∷ []) [] (lit-pt d) nilD)))

  parse : G (a ∷ b ∷ d ∷ d ∷ [])
  parse = ⊗pt ＂ a ＂ Tail (a ∷ []) (b ∷ d ∷ d ∷ []) (lit-pt a)
            (⊗pt Alt Ds (b ∷ []) (d ∷ d ∷ []) (Sum.inl (lit-pt b)) ds)

  -- The point of the file: no projection out of `parse` appears here.
  _ : display (a ∷ b ∷ d ∷ d ∷ []) parse ≡ "abdd"
  _ = refl

  -- the other summand, same printer
  parse' : G (a ∷ c ∷ [])
  parse' = ⊗pt ＂ a ＂ Tail (a ∷ []) (c ∷ []) (lit-pt a)
             (⊗pt Alt Ds (c ∷ []) [] (Sum.inr (lit-pt c)) nilD)

  _ : display (a ∷ c ∷ []) parse' ≡ "ac"
  _ = refl

  -- `⊤Ty` prints its index, through `read`.
  _ : display {A = ⊤Ty} (text "hello") tt ≡ "hello"
  _ = refl

  -- `char *`, resolved from `Display-char` and `Display-*`
  chars : (char *) (ch 'x' ∷ ch 'y' ∷ [])
  chars =
    CONS {A = char} _
      (⊗pt char (char *) (ch 'x' ∷ []) (ch 'y' ∷ []) (ch 'x' , Eq.refl)
        (CONS {A = char} _
          (⊗pt char (char *) (ch 'y' ∷ []) [] (ch 'y' , Eq.refl)
            (NIL {A = char} [] (lift εTy-pt)))))

  _ : display (ch 'x' ∷ ch 'y' ∷ []) chars ≡ "xy"
  _ = refl

  -- `String*`, whose instance is bespoke because it is a `μ`
  _ : display {A = String*} (text "hi") (read (text "hi") tt) ≡ "hi"
  _ = refl

  -- A dependent sum, with the record passed explicitly.  This is the
  -- fallback the header warns about: `⊕ᴰ` has no instance, on purpose.
  Sel : Bool → TheoryTy _ tt
  Sel false = ＂ a ＂
  Sel true = ＂ b ＂

  selDisplay : (x : Bool) → Display (Sel x)
  selDisplay false = theDisplay
  selDisplay true = theDisplay

  Tagged : TheoryTy _ tt
  Tagged = ⊕[ x ∈ Bool ] Sel x

  showBool : Bool → AS.String
  showBool false = "0:"
  showBool true = "1:"

  _ : display {A = Tagged} {{displayΣ-tagged showBool selDisplay}}
        (b ∷ []) (true , lit-pt b)
      ≡ "1:b"
  _ = refl

------------------------------------------------------------------------
-- ...and the same class on a real regex parse.
--
-- `decide-r` produces the parse; nothing below projects out of it.  The
-- instance for `ty ⟦ ident ⟧` is assembled from `Display-satG`,
-- `Display-⊕`, `Display-⊗`, `Display-lit` and `Display-*`.

module RegexDemo where

  open RU

  showU : UChar → AS.String
  showU c = untext (c ∷ [])

  ℓr : Level
  ℓr = ℓ-suc ℓ-zero

  open SatDisplay UChar _≟U_ ℓr showU

  -- `[[:alpha:]_][[:alnum:]_]*`
  ident : RE notNullable
  ident = (alphaR ⊕r charR '_') ⊗r ((alnumR ⊕r charR '_') *r)

  parsed : ty ⟦ ident ⟧ (text "x1_")
  parsed = theYes (decide-r ident ℓr (text "x1_") tt) Eq.refl

  _ : display (text "x1_") parsed ≡ "x1_"
  _ = refl
