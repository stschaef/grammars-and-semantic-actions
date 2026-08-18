-- ⊤ is an intial algebra
-- TODO is this used?
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
import Cubical.Algebra.Theory.Finitary.Free.Closing as Cl
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Top.Initial
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq
open import Cubical.Data.Unit using (tt)
open import Cubical.WildCat.LocallySmall.Base

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Top.Base σeq V vs 𝒫
open import Theory.Type.Top.Properties σeq V vs 𝒫 using (≅⊤Ty)

private variable ℓA ℓSem : Level

module Splitting {Sem : S → Type ℓSem} (isSetSem : (s : S) → isSet (Sem s))
  (semOps : Ops {σ = σ} Sem)
  (semSat : (e : σeq .eqns)
            (ρ : (w : vars σeq e) → Sem (σeq .varSort e w))
          → TmRec Sem semOps ρ (σeq .lhs e) ≡ TmRec Sem semOps ρ (σeq .rhs e))
  (semGen : (v : V) → Sem (vs v))
  (down : (s : S) → Sem s → ↓M s)
  (down-op : (o : σ .ops) (ys : (a : arities σ o) → Sem (σ .sortOf o a))
           → down (σ .resultSort o) (semOps o ys)
             ≡ op o (λ a → down (σ .sortOf o a) (ys a)))
  (down-gen : (v : V) → down (vs v) (semGen v) ≡ ⌈gen v ⌉)
  where

  split : {s : S} → ↓M s → Sem s
  split = Pres.rec 𝒫 isSetSem semOps semSat semGen

  splits : {s : S} (m : ↓M s) → down s (split m) ≡ m
  splits m =
    Pres.recUniq 𝒫 (λ s → M .fst s .snd) op (M .snd .snd)
      (λ v → ⌈gen v ⌉)
      (λ s z → down s (split z))
      (λ o ms →
        cong (down (σ .resultSort o))
          (Pres.recOp 𝒫 isSetSem semOps semSat semGen o ms)
        ∙ down-op o (λ a → split (ms a)))
      (λ v →
        cong (down (vs v)) (Pres.recGen 𝒫 isSetSem semOps semSat semGen v)
        ∙ down-gen v)
      m
    ∙ sym
      (Pres.recUniq 𝒫 (λ s → M .fst s .snd) op (M .snd .snd)
        (λ v → ⌈gen v ⌉) (λ _ z → z) (λ o ms → refl) (λ v → refl) m)

  splitsEq : {s : S} (m : ↓M s) → down s (split m) Eq.≡ m
  splitsEq m = Eq.pathToEq (splits m)

Tot : ((s : S) → TheoryTy ℓA s) → S → Type _
Tot A s = Σ[ m ∈ ↓M s ] A s m

module Total {A : (s : S) → TheoryTy ℓA s}
  (isSetTot : (s : S) → isSet (Tot A s))
  (totOps : Ops {σ = σ} (Tot A))
  (totSat : (e : σeq .eqns)
            (ρ : (w : vars σeq e) → Tot A (σeq .varSort e w))
          → TmRec (Tot A) totOps ρ (σeq .lhs e)
            ≡ TmRec (Tot A) totOps ρ (σeq .rhs e))
  (totGen : (v : V) → Tot A (vs v))
  (totOps-fst : (o : σ .ops) (ys : (a : arities σ o) → Tot A (σ .sortOf o a))
    → totOps o ys .fst ≡ op o (λ a → ys a .fst))
  (totGen-fst : (v : V) → totGen v .fst ≡ ⌈gen v ⌉)
  where

  open Splitting isSetTot totOps totSat totGen
    (λ _ → fst) totOps-fst totGen-fst public

  private
    castA : {s : S} {m m' : ↓M s} → m Eq.≡ m' → A s m → A s m'
    castA Eq.refl a = a

  reify : (s : S) → ⊤Ty ⊢ A s
  reify s m _ = castA (splitsEq m) (split m .snd)

  ⊤≅ : ((s : S) (m : ↓M s) → isProp (A s m)) → (s : S) → ⊤Ty ≅ A s
  ⊤≅ isPropA s =
    ≅⊤Ty (reify s) (funExt λ m → funExt λ a → isPropA s m _ a)
