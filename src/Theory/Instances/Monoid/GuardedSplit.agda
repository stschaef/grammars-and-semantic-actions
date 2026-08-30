{- Reaching the delayed hypothesis through a binary splitting.

   `⊗-overSplit` is general for any signature, but its argument is a
   metalanguage function on slot contents, so every call site steps out of the
   DSL.  Here that is paid off: a caller supplies only the *payment* -- a proof
   that the slot it wants is a step down -- and gets a `⊢`-term back.

   The payment has to be a proof, not a term: it relates the point `ms a` to
   the point `m`, and a `⊢`-map preserves its index, so nothing internal can
   cross points.  Crossing points is exactly what the modality's `app` is for.

   This lives over `MonSig` rather than an arbitrary signature because naming
   the two slots needs `arity _⊙_` to be `2` definitionally.  Both theories
   that want it -- bags and strings -- are `MonSig` theories. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
open import Theory.Instances.Monoid.Base
module Theory.Instances.Monoid.GuardedSplit
  {ℓ'' ℓv ℓP}
  (σeq : SortedEqns MonSig ℓ'')
  (V : Type ℓv) (vs : V → Sorts)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt ; tt*)
import Cubical.Data.Equality as Eq

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Operation.Base σeq V vs 𝒫
open import Theory.Type.Product.Binary.Base σeq V vs 𝒫 using (_&_)
open import Theory.Type.Guarded.Base σeq V vs 𝒫

private variable ℓA ℓB ℓR ℓX : Level

-- the binary tensor of this signature: `⊎B` in the bag theory, `_⊗_` in the
-- string theory, the same expression in both
_⊛_ : TheoryTy ℓA tt → TheoryTy ℓB tt → TheoryTy _ tt
_⊛_ {ℓA = ℓA} {ℓB = ℓB} A B = ⊗[ _⊙_ ][ two ℓA ℓB ] (A , B , tt*)

infixr 20 _⊛_

module _ {C : (s : Sorts) → TheoryTy ℓA s}
  {R : Pt (λ s → s) → Pt (λ s → s) → Type ℓR} (L : Löb R C) where
  open Löb L

  -- what a caller owes to read the hypothesis at the right slot: the left
  -- slot's occupant must put the right one strictly below the whole
  PayR : {X : TheoryTy ℓX tt} → Type _
  PayR {X = X} = (m : ↓M tt) (ms : interpIn _⊙_ ↓M) → op _⊙_ ms Eq.≡ m
    → X (ms zero) → R (tt , ms (suc zero)) (tt , m)

  ▷⊛r : {X : TheoryTy ℓX tt} {B : TheoryTy ℓB tt}
    → PayR {X = X} → (X ⊛ B) & ▷ tt ⊢ X ⊛ (B & C tt)
  ▷⊛r pay = ⊗&-overSplit λ m ms e (x , b , tt*) β →
    x , (b , app (pay m ms e x) β) , tt*

  -- the same one level down: what the left slot leaves splits again, and both
  -- halves are below the whole
  PayR² : {X : TheoryTy ℓX tt} → Type _
  PayR² {X = X} = (m : ↓M tt) (ms ns : interpIn _⊙_ ↓M)
    → op _⊙_ ms Eq.≡ m → op _⊙_ ns Eq.≡ ms (suc zero) → X (ms zero)
    → R (tt , ns zero) (tt , m) × R (tt , ns (suc zero)) (tt , m)

  ▷⊛r² : {X : TheoryTy ℓX tt} {B B' : TheoryTy ℓB tt}
    → PayR² {X = X}
    → (X ⊛ (B ⊛ B')) & ▷ tt ⊢ X ⊛ ((B & C tt) ⊛ (B' & C tt))
  ▷⊛r² pay = ⊗&-overSplit λ m ms e (x , inner , tt*) β →
    x
    , ⊗-overSplit (ms (suc zero))
        (λ ns e' (b , b' , tt*) →
             (b , app (pay m ms ns e e' x .fst) β)
           , (b' , app (pay m ms ns e e' x .snd) β)
           , tt*)
        inner
    , tt*
