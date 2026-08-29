{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Two disciplines, one syntax, one set of combinators.

   Each test reports `(intuitionistic , linear)`.  Where they agree the
   term is linear; where they differ it is the discipline talking, not the
   framework -- both checkers are `fix step` over the same node cover, and
   the only difference is what the `Slots` say. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Annotated.LinearTests where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Sum as Sum

open import Theory.Instances.Annotated.Linear
import Theory.Instances.Annotated.Typing as T

import Theory.Combinator.Answer.Decidable
  AEqns ℕ (λ _ → nm) aPresentation as D
import Theory.Combinator.Answer.Incomplete
  AEqns ℕ (λ _ → nm) aPresentation as MB
import Theory.Combinator.Answer.NonDet
  AEqns ℕ (λ _ → nm) aPresentation as NDm

module LinD = Check D.DecAnswer
module LinM = Check MB.MaybeAnswer
module LinN = Check NDm.NDAnswer
module IntD = T.Check D.DecAnswer

-- readouts
linB : Ctx → Ty → ATm → Bool
linB Γ A t = Sum.rec (λ _ → true) (λ _ → false) (LinD.linear (Γ , A) t tt)

intB : Ctx → Ty → ATm → Bool
intB Γ A t = Sum.rec (λ _ → true) (λ _ → false) (IntD.typed (Γ , A) t tt)

mayB : Ctx → Ty → ATm → Bool
mayB Γ A t = Sum.rec (λ _ → true) (λ _ → false) (LinM.linear (Γ , A) t tt)

count : Ctx → Ty → ATm → ℕ
count Γ A t = length (NDm.ndToList t (LinN.linear (Γ , A) t tt))

-- both : reports (intuitionistic , linear)
both : Ctx → Ty → ATm → Bool × Bool
both Γ A t = intB Γ A t , linB Γ A t

-- terms
idT : ATm                        -- λx:ι. x
idT = alam 0 ι (avar 0)

konst : ATm                      -- λx:ι. λy:ι. x        (y unused)
konst = alam 0 ι (alam 1 ι (avar 0))

nested : ATm                     -- λf:ι⇒ι. λx:ι. f x
nested = alam 0 (ι ⇒ ι) (alam 1 ι (aapp ι (avar 0) (avar 1)))

dbl : ATm                        -- λf:ι⇒ι. λx:ι. f (f x)   (f used twice)
dbl = alam 0 (ι ⇒ ι)
        (alam 1 ι (aapp ι (avar 0) (aapp ι (avar 0) (avar 1))))

drop : ATm                       -- λf:ι⇒ι. λx:ι. x         (f unused)
drop = alam 0 (ι ⇒ ι) (alam 1 ι (avar 1))


-- Where the two agree: every binding used exactly once.
agree-id : both [] (ι ⇒ ι) idT ≡ (true , true)
agree-id = refl

agree-nested : both [] ((ι ⇒ ι) ⇒ ι ⇒ ι) nested ≡ (true , true)
agree-nested = refl

-- Where they differ: weakening.  `konst` discards `y`.
differ-konst : both [] (ι ⇒ ι ⇒ ι) konst ≡ (true , false)
differ-konst = refl

differ-drop : both [] ((ι ⇒ ι) ⇒ ι ⇒ ι) drop ≡ (true , false)
differ-drop = refl

-- ...and contraction.  `dbl` uses `f` twice.
differ-dbl : both [] ((ι ⇒ ι) ⇒ ι ⇒ ι) dbl ≡ (true , false)
differ-dbl = refl

-- Both still reject the genuinely ill-typed.
agree-bad : both [] ι idT ≡ (false , false)
agree-bad = refl

-- A free variable must be consumed too: the ambient context is linear.
open-used : linB ((7 , ι) ∷ []) ι (avar 7) ≡ true
open-used = refl

open-unused : linB ((3 , ι) ∷ (7 , ι) ∷ []) ι (avar 7) ≡ false
open-unused = refl

-- ...and the application really does split it, rather than sharing it
split-ok : linB ((0 , ι ⇒ ι) ∷ (1 , ι) ∷ []) ι (aapp ι (avar 0) (avar 1)) ≡ true
split-ok = refl

split-bad : linB ((0 , ι ⇒ ι) ∷ []) ι (aapp ι (avar 0) (avar 0)) ≡ false
split-bad = refl

-- The other two answers, on the same grammar.
may-nested : mayB [] ((ι ⇒ ι) ⇒ ι ⇒ ι) nested ≡ true
may-nested = refl

may-konst : mayB [] (ι ⇒ ι ⇒ ι) konst ≡ false
may-konst = refl

nd-nested : count [] ((ι ⇒ ι) ⇒ ι ⇒ ι) nested ≡ 1
nd-nested = refl

nd-konst : count [] (ι ⇒ ι ⇒ ι) konst ≡ 0
nd-konst = refl
