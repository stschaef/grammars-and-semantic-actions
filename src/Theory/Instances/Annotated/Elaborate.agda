{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- What proof-relevance buys: the checker stops saying yes and starts
   producing a program.

   `Der (Γ , A) t` is a derivation, and a derivation is data.  Folding it
   gives the elaborated core term -- named variables resolved to de Bruijn
   indices, annotations kept, side conditions discarded.  The fold is
   structural on the term, and the variable case is where the work already
   happened: `deBruijn` reads the index off the `Lookup` witness the
   checker built, rather than searching the context again.

   That is the difference between a judgment defined as `lookC Γ x ≡ just A`
   and one defined as `Lookup Γ A x`.  Both are propositions and both say
   the same thing; only the second *carries* what a compiler needs. -}
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

import Theory.Combinator.Answer.Decidable
  AEqns ℕ (λ _ → nm) aPresentation as D

module CD = Check D.DecAnswer

-- The core language: the same calculus with variables resolved.
data CoreTm : Type ℓ-zero where
  cvar : ℕ → CoreTm
  capp : CoreTm → CoreTm → CoreTm
  clam : Ty → CoreTm → CoreTm

-- The fold.  Note there is no failure case: a derivation is a proof the
-- term checks, so elaboration is total on derivations.
elab : (i : Jdg) (t : ATm) → Der i t → CoreTm
elab (Γ , A) (avar x) v = cvar (deBruijn Γ A x v)
elab (Γ , A) (aapp B f a) d =
  capp (elab (Γ , B ⇒ A) f (d .fst)) (elab (Γ , B) a (d .snd))
elab (Γ , A) (alam x B t) d =
  clam B (elab ((x , B) ∷ Γ , cod A) t (d .snd))

-- Check, then elaborate.  This is the front end: source term in, core term
-- or a rejection out.
compile : (Γ : Ctx) (A : Ty) (t : ATm) → Maybe CoreTm
compile Γ A t = onDec (CD.typed (Γ , A) t tt)
  where
  onDec : DecTy (Der (Γ , A)) t → Maybe CoreTm
  onDec (Sum.inl d) = just (elab (Γ , A) t d)
  onDec (Sum.inr _) = nothing


-- Tests.  `refl` again, so the typechecker runs the whole front end.

idT : ATm
idT = alam 0 ι (avar 0)

konst : ATm                             -- λx:ι. λy:ι. x
konst = alam 0 ι (alam 1 ι (avar 0))

shadow : ATm                            -- λx:ι. λx:ι. x
shadow = alam 0 ι (alam 0 ι (avar 0))

nested : ATm                            -- λf:ι⇒ι. λx:ι. f x
nested = alam 0 (ι ⇒ ι) (alam 1 ι (aapp ι (avar 0) (avar 1)))

elab-id : compile [] (ι ⇒ ι) idT ≡ just (clam ι (cvar 0))
elab-id = refl

-- the outer binder, so index 1: the fold read this off the derivation
elab-konst : compile [] (ι ⇒ ι ⇒ ι) konst ≡ just (clam ι (clam ι (cvar 1)))
elab-konst = refl

-- ...and shadowing resolves inward, so the *same* source name gives 0
elab-shadow : compile [] (ι ⇒ ι ⇒ ι) shadow ≡ just (clam ι (clam ι (cvar 0)))
elab-shadow = refl

elab-nested : compile [] ((ι ⇒ ι) ⇒ ι ⇒ ι) nested
            ≡ just (clam (ι ⇒ ι) (clam ι (capp (cvar 1) (cvar 0))))
elab-nested = refl

-- a free variable resolves against the ambient context
elab-open : compile ((7 , ι) ∷ []) ι (avar 7) ≡ just (cvar 0)
elab-open = refl

elab-open2 : compile ((3 , ι) ∷ (7 , ι) ∷ []) ι (avar 7) ≡ just (cvar 1)
elab-open2 = refl

-- ill-typed terms produce nothing, not a bad core term
elab-bad : compile [] ι idT ≡ nothing
elab-bad = refl
