{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- What the generic combinators ask of the annotated lambda theory:
   precision of every operation, and a well-founded order for the guard.

   Identical in shape to `Instances/Lambda/Guard`, and for the same reason:
   a free term algebra is precise everywhere and its subterm order is its
   size.  There is no `headClash` here -- `Typing` unrolls a term to *one*
   node rather than to a sum over head constructors, because the operations
   `appOp B` and `lamOp B` are indexed by a type and so there are infinitely
   many of them.  That is what `Core`'s pointwise `Ans-mapAt` is for. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Type.Later.Indexed as LI
module Theory.Instances.Annotated.Guard where

open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-comm ; +-suc)
import Cubical.Data.Nat.Order as NO
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Sigma using (ΣPathP ; _,_ ; fst ; snd)
import Cubical.Data.Sum as Sum
import Cubical.Data.Equality as Eq

open import Theory.Instances.Annotated.Base public
open import Theory.Base AEqns ℕ (λ _ → nm) aPresentation public
open import Theory.Type.HLevels AEqns ℕ (λ _ → nm) aPresentation public
open import Theory.Type.Top.Base AEqns ℕ (λ _ → nm) aPresentation public
open import Theory.Type.Bottom.Base AEqns ℕ (λ _ → nm) aPresentation public
open import Theory.Type.Sum.Binary.Base AEqns ℕ (λ _ → nm) aPresentation public
open import Theory.Type.Product.Binary.Base AEqns ℕ (λ _ → nm) aPresentation public
open import Theory.Combinator.Core AEqns ℕ (λ _ → nm) aPresentation public

private variable ℓX : Level

-- Constructor injectivity, by projection.  Public, because `Typing`'s
-- roll needs them too: matching `Eq.refl` on `op (appOp B) ms ≡ aapp B f a`
-- is stuck without K -- the annotation `B` occurs both as the operation's
-- index and as a constructor argument -- so the equations are projected out
-- rather than matched.
varN : ℕ → ATm → ℕ
varN d (avar x) = x
varN d (aapp _ _ _) = d
varN d (alam _ _ _) = d
appFun appArgOf : ATm → ATm
appFun (avar x) = avar x
appFun (aapp _ f _) = f
appFun (alam x B t) = alam x B t
appArgOf (avar x) = avar x
appArgOf (aapp _ _ a) = a
appArgOf (alam x B t) = alam x B t

lamN : ℕ → ATm → ℕ
lamN d (avar _) = d
lamN d (aapp _ _ _) = d
lamN d (alam x _ _) = x

lamBd : ATm → ATm
lamBd (avar x) = avar x
lamBd (aapp B f a) = aapp B f a
lamBd (alam _ _ t) = t

preciseA : (o : AOp) → Precise o
preciseA varOp m (ms , e) (ms' , e') =
  ΣPathP (funExt slot , isProp→PathP (λ _ → isPropModelEq) e e')
  where
  whole : avar (ms zero) ≡ avar (ms' zero)
  whole = Eq.eqToPath e ∙ sym (Eq.eqToPath e')

  slot : (a : Fin 1) → ms a ≡ ms' a
  slot zero = cong (varN (ms zero)) whole
preciseA (appOp B) m (ms , e) (ms' , e') =
  ΣPathP (funExt slot , isProp→PathP (λ _ → isPropModelEq) e e')
  where
  whole : aapp B (ms zero) (ms (suc zero)) ≡ aapp B (ms' zero) (ms' (suc zero))
  whole = Eq.eqToPath e ∙ sym (Eq.eqToPath e')

  slot : (a : Fin 2) → ms a ≡ ms' a
  slot zero = cong appFun whole
  slot (suc zero) = cong appArgOf whole
preciseA (lamOp B) m (ms , e) (ms' , e') =
  ΣPathP (funExt slot , isProp→PathP (λ _ → isPropModelEq) e e')
  where
  whole : alam (ms zero) B (ms (suc zero)) ≡ alam (ms' zero) B (ms' (suc zero))
  whole = Eq.eqToPath e ∙ sym (Eq.eqToPath e')

  slot : (a : Fin 2) → ms a ≡ ms' a
  slot zero = cong (lamN (ms zero)) whole
  slot (suc zero) = cong lamBd whole

-- The measure.
aSize : ATm → ℕ
aSize (avar _) = 1
aSize (aapp _ f a) = suc (aSize f + aSize a)
aSize (alam _ _ t) = suc (aSize t)

private
  fun< : (B : Ty) (f a : ATm) → aSize f NO.< aSize (aapp B f a)
  fun< B f a = aSize a , (+-suc (aSize a) (aSize f)
    ∙ cong suc (+-comm (aSize a) (aSize f)))

  arg< : (B : Ty) (f a : ATm) → aSize a NO.< aSize (aapp B f a)
  arg< B f a = aSize f , +-suc (aSize f) (aSize a)

  body< : (x : ℕ) (B : Ty) (t : ATm) → aSize t NO.< aSize (alam x B t)
  body< x B t = 0 , refl

module Subterm {X : Type ℓX} (isSetX : isSet X) (rank : X → ℕ) where

  srt : X → ASort
  srt _ = tm

  order : LI.IPtOrder AEqns ℕ (λ _ → nm) aPresentation srt ℓ-zero
  order = LI.ilexOrder AEqns ℕ (λ _ → nm) aPresentation srt
    isSetX (λ _ → aSize) rank

  open LI.IPtOrder order using (_<_) public

  smaller : {x x' : X} {t t' : ATm}
    → aSize t' NO.< aSize t → (x' , t') < (x , t)
  smaller lt = lift (Sum.inl lt)

  callFun : {x x' : X} (B : Ty) (f a : ATm) → (x' , f) < (x , aapp B f a)
  callFun B f a = smaller (fun< B f a)

  callArg : {x x' : X} (B : Ty) (f a : ATm) → (x' , a) < (x , aapp B f a)
  callArg B f a = smaller (arg< B f a)

  callBody : {x x' : X} (n : ℕ) (B : Ty) (t : ATm)
    → (x' , t) < (x , alam n B t)
  callBody n B t = smaller (body< n B t)
