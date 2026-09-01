{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `Phase/Display` at Unicode: instance-resolved pretty-printing of parses,
   and `SatDisplay` rendering a regex parse back to its input. -}
open import Cubical.Foundations.Prelude

module Examples.Theory.Phase.Display where

open import Cubical.Data.Unit using (tt ; tt*)
open import Cubical.Data.Sigma using (_,_ ; fst)
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

module Demo where

  open import Cubical.Data.Unicode
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

  -- `op _⊙_ (two x y)` reduces to `x ++ y`, so the index equation is `Eq.refl`.
  lit-pt : (x : UChar) → ＂ x ＂ (x ∷ [])
  lit-pt x = Eq.refl

  -- `A`/`B` explicit: implicit args under an application block pattern unification.
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

  _ : display (a ∷ b ∷ d ∷ d ∷ []) parse ≡ "abdd"
  _ = refl

  parse' : G (a ∷ c ∷ [])
  parse' = ⊗pt ＂ a ＂ Tail (a ∷ []) (c ∷ []) (lit-pt a)
             (⊗pt Alt Ds (c ∷ []) [] (Sum.inr (lit-pt c)) nilD)

  _ : display (a ∷ c ∷ []) parse' ≡ "ac"
  _ = refl

  _ : display {A = ⊤Ty} (text "hello") tt ≡ "hello"
  _ = refl

  chars : (char *) (ch 'x' ∷ ch 'y' ∷ [])
  chars =
    CONS {A = char} _
      (⊗pt char (char *) (ch 'x' ∷ []) (ch 'y' ∷ []) (ch 'x' , Eq.refl)
        (CONS {A = char} _
          (⊗pt char (char *) (ch 'y' ∷ []) [] (ch 'y' , Eq.refl)
            (NIL {A = char} [] (lift εTy-pt)))))

  _ : display (ch 'x' ∷ ch 'y' ∷ []) chars ≡ "xy"
  _ = refl

  _ : display {A = String*} (text "hi") (read (text "hi") tt) ≡ "hi"
  _ = refl

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
