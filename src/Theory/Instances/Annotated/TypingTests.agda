{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- One type checker, three answers.  The tests are `refl`, so the
   typechecker runs them. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Annotated.TypingTests where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Sum as Sum

open import Theory.Instances.Annotated.Typing

import Theory.Combinator.Answer.Decidable
  AEqns ℕ (λ _ → nm) aPresentation as D
import Theory.Combinator.Answer.Incomplete
  AEqns ℕ (λ _ → nm) aPresentation as MB
import Theory.Combinator.Answer.NonDet
  AEqns ℕ (λ _ → nm) aPresentation as NDm

module CD = Check D.DecAnswer
module CM = Check MB.MaybeAnswer
module CN = Check NDm.NDAnswer

-- the same grammar, read three ways
decideTy : (i : Idx) → D.Decidable (Der i)
decideTy = CD.typed

testTy : (i : Idx) → ⊤Ty ⊢ MB.Maybe (Der i)
testTy = CM.typed

parsesTy : (i : Idx) → ⊤Ty ⊢ NDm.ND (Der i)
parsesTy = CN.typed

decB : Ctx → Ty → ATm → Bool
decB Γ A t = Sum.rec (λ _ → true) (λ _ → false) (decideTy (Γ , A) t tt)

mayB : Ctx → Ty → ATm → Bool
mayB Γ A t = Sum.rec (λ _ → true) (λ _ → false) (testTy (Γ , A) t tt)

count : Ctx → Ty → ATm → ℕ
count Γ A t = length (NDm.ndToList t (parsesTy (Γ , A) t tt))

-- terms
idT : Ty → ATm
idT B = alam 0 B (avar 0)

konst : ATm
konst = alam 0 ι (alam 1 ι (avar 0))

selfId : ATm                                 -- (λx:ι. x) y
selfId = aapp ι (idT ι) (avar 1)

badDom : ATm                                 -- (λx:ι⇒ι. x) y   with y : ι
badDom = aapp ι (alam 0 (ι ⇒ ι) (avar 0)) (avar 1)

nested : ATm                                 -- λf:ι⇒ι. λx:ι. f x
nested = alam 0 (ι ⇒ ι) (alam 1 ι (aapp ι (avar 0) (avar 1)))

-- ...and the checks
dec-id : decB [] (ι ⇒ ι) (idT ι) ≡ true
dec-id = refl

dec-id-poly : decB [] ((ι ⇒ ι) ⇒ (ι ⇒ ι)) (idT (ι ⇒ ι)) ≡ true
dec-id-poly = refl

-- the annotation must match the type checked against
dec-id-wrong-dom : decB [] ((ι ⇒ ι) ⇒ (ι ⇒ ι)) (idT ι) ≡ false
dec-id-wrong-dom = refl

-- ...and the result type must be an arrow at all
dec-id-not-arrow : decB [] ι (idT ι) ≡ false
dec-id-not-arrow = refl

dec-konst : decB [] (ι ⇒ ι ⇒ ι) konst ≡ true
dec-konst = refl

-- shadowing: `konst`'s body returns the *outer* binder, so the type is
-- `ι ⇒ ι ⇒ ι` and not something else
dec-konst-wrong : decB [] (ι ⇒ (ι ⇒ ι) ⇒ ι) konst ≡ false
dec-konst-wrong = refl

dec-app : decB ((1 , ι) ∷ []) ι selfId ≡ true
dec-app = refl

dec-app-open : decB [] ι selfId ≡ false
dec-app-open = refl

-- the function's domain annotation disagrees with the application's
dec-bad-dom : decB ((1 , ι) ∷ []) ι badDom ≡ false
dec-bad-dom = refl

dec-nested : decB [] ((ι ⇒ ι) ⇒ ι ⇒ ι) nested ≡ true
dec-nested = refl

-- `Maybe` agrees
may-id : mayB [] (ι ⇒ ι) (idT ι) ≡ true
may-id = refl

may-nested : mayB [] ((ι ⇒ ι) ⇒ ι ⇒ ι) nested ≡ true
may-nested = refl

may-bad-dom : mayB ((1 , ι) ∷ []) ι badDom ≡ false
may-bad-dom = refl

-- ...and `ND` finds exactly one derivation, since typing is a proposition:
-- an annotated term has at most one derivation at a given type.
nd-id : count [] (ι ⇒ ι) (idT ι) ≡ 1
nd-id = refl

nd-nested : count [] ((ι ⇒ ι) ⇒ ι ⇒ ι) nested ≡ 1
nd-nested = refl

nd-app : count ((1 , ι) ∷ []) ι selfId ≡ 1
nd-app = refl

nd-bad-dom : count ((1 , ι) ∷ []) ι badDom ≡ 0
nd-bad-dom = refl

nd-not-arrow : count [] ι (idT ι) ≡ 0
nd-not-arrow = refl
