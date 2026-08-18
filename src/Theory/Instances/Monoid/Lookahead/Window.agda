{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- Lookahead of a fixed width: the truncation monoid Σ*/≡ₖ and the fibres
   of its classifying map, generalising `Lookahead.Base` from n = 1.

   `Window n` is the words of length at most n, and a *short* window carries
   more information than a full one: if the window did not fill then the
   input ended, so `Λw ⟨⟩` is `εTy` when budget remains and `⊤Ty` when it
   does not.  That asymmetry is forced -- without it a short window and a
   full one would overlap and there would be no cover.

   Disjointness is not a case analysis on pairs of windows: it is one
   induction, `Λw-sound`, reading the window back off the input.  Totality
   is structural on the input, so a table built from this reduces on a
   canonical string.

   The width is its own unary type rather than `ℕ`, because
   `Monoid.Base` re-exports `FinData`'s `zero`/`suc` and an `ℕ` pattern
   will not resolve downstream of it. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Lookahead.Window
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

import Cubical.Data.Empty as Empty
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt ; tt*)
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Type.Cover.Base MonEqns Alphabet (λ _ → tt) listPresentation

-- the lookahead width, as a unary numeral
data Width : Type ℓ-zero where
  none : Width
  more : Width → Width

w1 w2 w3 : Width
w1 = more none
w2 = more w1
w3 = more w2

-- a word of length at most n: the input, truncated to a n-token window
data Window : Width → Type ℓAlph where
  ⟨⟩  : {n : Width} → Window n
  _◂_ : {n : Width} → Alphabet → Window n → Window (more n)

infixr 5 _◂_

-- The fibres.  A full window says only what the input starts with; an
-- unfilled one says the input stopped there; and at width `none` there is
-- one window and it says nothing at all.
Λw : {n : Width} → Window n → TheoryTy ℓM tt
Λw {n = none}   ⟨⟩ = LiftTheoryTy ℓM ⊤Ty
Λw {n = more _} ⟨⟩ = εTy
Λw (c ◂ w) = literal c ⊗ Λw w

-- Reading the window off the input.  This is a metalanguage function on
-- a model element, so it stays private: it is how disjointness is
-- *proved*, and no client may see it or reason with it.  Everything this
-- module exports -- `Λw`, `windowCover`, `Λw-head` -- is internal.
private
  win : (n : Width) → ↓M tt → Window n
  win none _ = ⟨⟩
  win (more n) [] = ⟨⟩
  win (more n) (c ∷ m) = c ◂ win n m

  -- Every member of a fibre reads back to that fibre's window, which is
  -- one induction where comparing windows pairwise would be a case
  -- analysis with a transport in the recursive case.
  Λw-sound : {n : Width} (w : Window n) (m : ↓M tt) → Λw w m → win n m Eq.≡ w
  Λw-sound {n = none} ⟨⟩ m _ = Eq.refl
  Λw-sound {n = more n} ⟨⟩ .[] (_ , Eq.refl , _) = Eq.refl
  Λw-sound {n = more n} (c ◂ w) m (ms , e , (lc , (v , _))) =
    go (ms zero) (ms (suc zero)) lc e v
    where
    go : (u u' : ↓M tt) → u Eq.≡ (c ∷ []) → (u ++ u') Eq.≡ m → Λw w u'
       → win (more n) m Eq.≡ (c ◂ w)
    go .(c ∷ []) u' Eq.refl Eq.refl v' = Eq.ap (c ◂_) (Λw-sound w u' v')

Λw-disjoint : {n : Width} → Disjoint (Λw {n})
Λw-disjoint w w' ne m (v , v') =
  Empty.rec (ne (Eq.sym (Λw-sound w m v) Eq.∙ Λw-sound w' m v'))

-- Totality is structural recursion on the input, so every index equation
-- is `Eq.refl` and the dispatch reduces on a canonical string.
Λw-total : {n : Width} → Total (Λw {n})
Λw-total {n = none} m _ = ⟨⟩ , lift tt
Λw-total {n = more n} [] _ = ⟨⟩ , ((λ ()) , Eq.refl , tt*)
Λw-total {n = more n} (c ∷ m) _ = go (Λw-total {n = n} m tt)
  where
  go : (Σ[ w ∈ Window n ] Λw w m) → Σ[ w ∈ Window (more n) ] Λw w (c ∷ m)
  go (w , v) = (c ◂ w) , (two (c ∷ []) m , Eq.refl , (Eq.refl , (v , tt*)))


windowCover : (n : Width) → Cover (Window n) (Λw {n})
windowCover n .disjoint = Λw-disjoint
windowCover n .total = Λw-total

-- A full window names the next letter, and says so by forgetting the
-- rest of itself: the guard *is* `literal c ⊗ _`, so no equation on
-- windows is needed.  This is the only place the width reaches a table.
Λw-head : {n : Width} (c : Alphabet) (w : Window n)
  → Λw (c ◂ w) ⊢ literal c ⊗ ⊤Ty
Λw-head c w =
  _,⊗_ {A = literal c} {B = Λw w} {C = literal c} {D = ⊤Ty} id⊢ ⊤Ty-intro
