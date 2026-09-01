{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The elaborator is a projection, not a fold: `Der (Γ , A) t` is
   `Σ[ c ∈ Core Γ A ] (erase c ≡ t)`, so `elab = fst`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Annotated.Elaborate where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Sum as Sum

open import Theory.Instances.Annotated.Typing public

open import Theory.Type.SemanticAction.Base
  AEqns ℕ (λ _ → nm) aPresentation
import Theory.Combinator.Answer.Incomplete
  AEqns ℕ (λ _ → nm) aPresentation as MB
import Theory.Combinator.Answer.NonDet
  AEqns ℕ (λ _ → nm) aPresentation as NDm
import Theory.Combinator.Answer.Decidable
  AEqns ℕ (λ _ → nm) aPresentation as D

module CD = Check D.DecAnswer
module CM = Check MB.MaybeAnswer
module CN = Check NDm.NDAnswer

elab : (i : Jdg) (t : ATm) → Der i t → Core (i .fst) (i .snd)
elab i t d = d .fst

elabErase : (i : Jdg) (t : ATm) (d : Der i t) → erase (elab i t d) ≡ t
elabErase i t d = d .snd

-- de Bruijn index = number of "not here" steps in the `Lookup`.
data Nameless : Type ℓ-zero where
  dvar : ℕ → Nameless
  dapp : Nameless → Nameless → Nameless
  dlam : Ty → Nameless → Nameless

dB : {Γ : Ctx} {A : Ty} → Core Γ A → Nameless
dB (cvar {Γ = Γ} {A = A} x v) = dvar (deBruijn Γ A x v)
dB (capp f a) = dapp (dB f) (dB a)
dB (clam {B = B} x c) = dlam B (dB c)

elabAction : (i : Jdg) → SemanticAction (Der i) Nameless
elabAction i t d = dB (elab i t d) , tt

compile : (Γ : Ctx) (A : Ty) → ATm → Maybe Nameless
compile Γ A = observe (CD.typed (Γ , A)) (semact-dec (elabAction (Γ , A)))

-- `compileAll` is the empirical form of `isPropDer`; see `shadow`.
compileM : (Γ : Ctx) (A : Ty) → ATm → Maybe Nameless
compileM Γ A = observe (CM.typed (Γ , A)) (semact-Maybe (elabAction (Γ , A)))

compileAll : (Γ : Ctx) (A : Ty) → ATm → List Nameless
compileAll Γ A = NDm.observeND (CN.typed (Γ , A)) (elabAction (Γ , A))

idT : ATm
idT = alam 0 ι (avar 0)

konst : ATm                             -- λx:ι. λy:ι. x
konst = alam 0 ι (alam 1 ι (avar 0))

shadow : ATm                            -- λx:ι. λx:ι. x
shadow = alam 0 ι (alam 0 ι (avar 0))

nested : ATm                            -- λf:ι⇒ι. λx:ι. f x
nested = alam 0 (ι ⇒ ι) (alam 1 ι (aapp ι (avar 0) (avar 1)))

elab-id : compile [] (ι ⇒ ι) idT ≡ just (dlam ι (dvar 0))
elab-id = refl

elab-konst : compile [] (ι ⇒ ι ⇒ ι) konst ≡ just (dlam ι (dlam ι (dvar 1)))
elab-konst = refl

-- shadowing resolves inward: the same source name gives 0
elab-shadow : compile [] (ι ⇒ ι ⇒ ι) shadow ≡ just (dlam ι (dlam ι (dvar 0)))
elab-shadow = refl

elab-nested : compile [] ((ι ⇒ ι) ⇒ ι ⇒ ι) nested
            ≡ just (dlam (ι ⇒ ι) (dlam ι (dapp (dvar 1) (dvar 0))))
elab-nested = refl

elab-open : compile ((7 , ι) ∷ []) ι (avar 7) ≡ just (dvar 0)
elab-open = refl

elab-open2 : compile ((3 , ι) ∷ (7 , ι) ∷ []) ι (avar 7) ≡ just (dvar 1)
elab-open2 = refl

elab-bad : compile [] ι idT ≡ nothing
elab-bad = refl

may-nested : compileM [] ((ι ⇒ ι) ⇒ ι ⇒ ι) nested
           ≡ just (dlam (ι ⇒ ι) (dlam ι (dapp (dvar 1) (dvar 0))))
may-nested = refl

may-bad : compileM [] ι idT ≡ nothing
may-bad = refl

all-id : compileAll [] (ι ⇒ ι) idT ≡ dlam ι (dvar 0) ∷ []
all-id = refl

-- a `cvar` holding a bare numeral would list two core terms here
all-shadow : compileAll [] (ι ⇒ ι ⇒ ι) shadow ≡ dlam ι (dlam ι (dvar 0)) ∷ []
all-shadow = refl

all-nested : compileAll [] ((ι ⇒ ι) ⇒ ι ⇒ ι) nested
           ≡ dlam (ι ⇒ ι) (dlam ι (dapp (dvar 1) (dvar 0))) ∷ []
all-nested = refl

all-bad : compileAll [] ι idT ≡ []
all-bad = refl
