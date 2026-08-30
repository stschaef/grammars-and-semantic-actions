{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `Phase.Display`, exercised on hand-built parses.

   Each row prints a parse by running the grammar's own resolved
   `Display` action and states the text it should produce, so a `refl`
   here is instance resolution assembling a printer and then that printer
   computing.  `Connectives` covers the hand-built points; `Regex` covers
   a printer resolved for a regex through `SatDisplay`. -}
open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.Phase.DisplayTests where

open import Cubical.Data.Unit using (tt ; tt*)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Bool using (Bool ; true ; false)
import Cubical.Data.Sum as Sum
import Cubical.Data.Equality as Eq
import Agda.Builtin.String as AS


import Theory.Instances.Monoid.Base as MB
import Theory.Instances.Monoid.Strings as Str
import Theory.Instances.Monoid.KleeneStar as KS
import Theory.Instances.Monoid.SemanticAction as SA
import Theory.Instances.Monoid.Regex.Unicode as RU
open import Theory.Instances.Monoid.Phase.Display

module Connectives where

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

  parse' : G (a ∷ c ∷ [])
  parse' = ⊗pt ＂ a ＂ Tail (a ∷ []) (c ∷ []) (lit-pt a)
             (⊗pt Alt Ds (c ∷ []) [] (Sum.inr (lit-pt c)) nilD)

  chars : (char *) (ch 'x' ∷ ch 'y' ∷ [])
  chars =
    CONS {A = char} _
      (⊗pt char (char *) (ch 'x' ∷ []) (ch 'y' ∷ []) (ch 'x' , Eq.refl)
        (CONS {A = char} _
          (⊗pt char (char *) (ch 'y' ∷ []) [] (ch 'y' , Eq.refl)
            (NIL {A = char} [] (lift εTy-pt)))))

  ----------------------------------------------------------------------
  -- The printers resolution assembles for `⊗`, `⊕`, `*`, a literal and
  -- `char`.  Every answer is the word the parse is a parse of.

  connectives : passes
      ( display (a ∷ b ∷ d ∷ d ∷ []) parse    ↦ "abdd"
      ∷ display (a ∷ c ∷ []) parse'           ↦ "ac"
      ∷ display (ch 'x' ∷ ch 'y' ∷ []) chars  ↦ "xy"
      ∷ [])
  connectives = refl

  -- The two grammars whose parses carry nothing, so the printer has to go
  -- through the index: `⊤Ty`, and `String*`, whose instance is bespoke
  -- because it is a `μ`.
  whole-word : passes
      ( display {A = ⊤Ty} (text "hello") tt                     ↦ "hello"
      ∷ display {A = String*} (text "hi") (read (text "hi") tt) ↦ "hi"
      ∷ [])
  whole-word = refl

  ----------------------------------------------------------------------
  -- A dependent sum, with the record passed explicitly.  This is the
  -- fallback `Phase/Display`'s header warns about: `⊕ᴰ` has no instance,
  -- on purpose.

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

  tagged-sum : passes
      ( display {A = Tagged} {{displayΣ-tagged showBool selDisplay}}
          (b ∷ []) (true , lit-pt b)
        ↦ "1:b"
      ∷ [])
  tagged-sum = refl

module Regex where

  open RU

  showU : UChar → AS.String
  showU c = untext (c ∷ [])

  ℓr : Level
  ℓr = ℓ-suc ℓ-zero

  open SatDisplay UChar _≟U_ ℓr showU

  -- `[[:alpha:]_][[:alnum:]_]*`
  ident : RE notNullable
  ident = (alphar ⊕r charr '_') ⊗r ((alnumr ⊕r charr '_') *r)

  parsed : ty ⟦ ident ⟧ (text "x1_")
  parsed = theYes (decide-r ident ℓr (text "x1_") tt) Eq.refl

  -- `ty ⟦ r ⟧` resolves for a regex only because `Display-satTy` exists;
  -- the printout is the matched text back again.
  identifiers : passes
      ( display (text "x1_") parsed ↦ "x1_"
      ∷ [])
  identifiers = refl
