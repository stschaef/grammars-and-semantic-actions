module Cubical.Data.Nat.WFOrder where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; suc ; isSetℕ)
open import Cubical.Data.Nat.Order using (_<_ ; isProp≤ ; <-trans ; <-wellfounded)
import Cubical.Data.Nat.Order.Recursive as R
open import Cubical.Categories.Direct.Base using (WFOrder)

ℕWF = record
  { D = ℕ ; isSetD = isSetℕ ; _<_ = _<_
  ; isProp< = λ _ _ → isProp≤ ; trans< = <-trans ; wf< = <-wellfounded }

ℕWFRec : WFOrder ℓ-zero ℓ-zero
ℕWFRec = record
  { D = ℕ ; isSetD = isSetℕ ; _<_ = R._<_
  ; isProp< = λ a b → R.isProp≤ {suc a} {b}
  ; trans< = λ {a} {b} {c} → R.<-trans {a} {b} {c}
  ; wf< = R.WellFounded.wf-< }
