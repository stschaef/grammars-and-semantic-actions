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


private variable ℓA ℓB : Level

appArgs : ↓M tm → ↓M tm → (b : Fin 2) → ↓M (LSortOf appOp b)
appArgs t u = two t u

lamArgs : ↓M nm → ↓M tm → (b : Fin 2) → ↓M (LSortOf lamOp b)
lamArgs n t = two n t
