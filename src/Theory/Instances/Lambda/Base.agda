open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns
module Theory.Instances.Lambda.Base
  (Name : Type ℓ-zero) (isSetName : isSet Name) where

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.FinData.More public
open import Cubical.Data.Unit using (Unit ; tt ; Unit* ; tt*)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma

open import Theory.Instances.Lambda.Signature public
open import Theory.Instances.Lambda.TermPresentation Name isSetName
  using (termPresentation ; RawTm ; tvar ; tapp ; tlam) public

open import Theory.Base λEqns Name (λ _ → nm) termPresentation public
open import Theory.Type.Lift.Base λEqns Name (λ _ → nm) termPresentation public
open import Theory.Type.Sum.Base λEqns Name (λ _ → nm) termPresentation public
open import Theory.Type.Operation.Base λEqns Name (λ _ → nm) termPresentation public
open import Theory.Type.Inductive.Base λEqns Name (λ _ → nm) termPresentation public

Raw : Type ℓM
Raw = ↓M tm

Nm : Type ℓM
Nm = ↓M nm

private variable ℓA ℓB ℓC ℓD : Level

mkVar : Nm → Raw
mkVar n = op varOp λ _ → n

appArgs : Raw → Raw → (b : Fin 2) → ↓M (LSortOf appOp b)
appArgs t u = two t u

lamArgs : Nm → Raw → (b : Fin 2) → ↓M (LSortOf lamOp b)
lamArgs n t = two n t

mkApp : Raw → Raw → Raw
mkApp t u = op appOp (appArgs t u)

mkLam : Nm → Raw → Raw
mkLam n t = op lamOp (lamArgs n t)

VarTy : TheoryTy ℓA nm → TheoryTy _ tm
VarTy {ℓA = ℓA} P = ⊗[ varOp ][ (λ _ → ℓA) ] (P , tt*)

AppTy : TheoryTy ℓA tm → TheoryTy ℓB tm → TheoryTy _ tm
AppTy {ℓA = ℓA} {ℓB = ℓB} A B =
  ⊗[ appOp ][ two ℓA ℓB ] (A , B , tt*)

LamTy : TheoryTy ℓA nm → TheoryTy ℓB tm → TheoryTy _ tm
LamTy {ℓA = ℓA} {ℓB = ℓB} P A =
  ⊗[ lamOp ][ two ℓA ℓB ] (P , A , tt*)

module _ {P : TheoryTy ℓA nm} {A : TheoryTy ℓB tm} {B : TheoryTy ℓC tm} where
  var-mk : {n : Nm} → P n → VarTy P (mkVar n)
  var-mk {n = n} p = (λ _ → n) , Eq.refl , p , tt*

  app-mk : {t u : Raw} → A t → B u → AppTy A B (mkApp t u)
  app-mk {t = t} {u = u} a b = appArgs t u , Eq.refl , a , b , tt*

  lam-mk : {n : Nm} {t : Raw} → P n → A t → LamTy P A (mkLam n t)
  lam-mk {n = n} {t = t} p a = lamArgs n t , Eq.refl , p , a , tt*

module _ {P : TheoryTy ℓA nm} {A : TheoryTy ℓB tm}
         {B : TheoryTy ℓC tm} {C : TheoryTy ℓD tm} where
  -- as for app and lam: `Fin 1` has no η, so the motive sees the tuple
  var-elim : ((ms : (b : Fin 1) → ↓M (LSortOf varOp b))
             → P (ms zero) → C (op varOp ms))
           → VarTy P ⊢ C
  var-elim f _ (ms , Eq.refl , p , tt*) = f ms p

  app-elim : ((ms : (b : Fin 2) → ↓M (LSortOf appOp b))
             → A (ms zero) → B (ms (suc zero)) → C (op appOp ms))
           → AppTy A B ⊢ C
  app-elim f _ (ms , Eq.refl , a , b , tt*) = f ms a b

  lam-elim : ((ms : (b : Fin 2) → ↓M (LSortOf lamOp b))
             → P (ms zero) → A (ms (suc zero)) → C (op lamOp ms))
           → LamTy P A ⊢ C
  lam-elim f _ (ms , Eq.refl , p , a , tt*) = f ms p a
