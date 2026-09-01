-- A presentation of the free model, chosen per instantiation.
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Equality as Eq
open Category
open SortedSig
open SortedEqns
module Theory.Free.Base
  {ℓ ℓ'' ℓv ℓS} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  where

record FreePresentation ℓP : Typeω where
  field
    P : MOD σeq ℓP .ob

  Carrier : S → Type ℓP
  Carrier s = P .fst s .fst

  isSetCarrier : (s : S) → isSet (Carrier s)
  isSetCarrier s = P .fst s .snd

  op : (o : σ .ops) → ((a : arities σ o) → Carrier (σ .sortOf o a))
     → Carrier (σ .resultSort o)
  op = P .snd .fst

  field
    -- equations but with Eq
    satStrict : (e : σeq .eqns)
        (ρ : (w : vars σeq e) → Carrier (σeq .varSort e w))
      → TmRec Carrier op ρ (σeq .lhs e) Eq.≡ TmRec Carrier op ρ (σeq .rhs e)

    gen : (v : V) → Carrier (vs v)

    rec : ∀ {ℓX} {X : S → Type ℓX} → ((s : S) → isSet (X s))
        → (α : Ops {σ = σ} X)
        → ((e : σeq .eqns) (ρ : (w : vars σeq e) → X (σeq .varSort e w))
            → TmRec X α ρ (σeq .lhs e) ≡ TmRec X α ρ (σeq .rhs e))
        → ((v : V) → X (vs v)) → {s : S} → Carrier s → X s

    recGen : ∀ {ℓX} {X : S → Type ℓX} (isSetX : (s : S) → isSet (X s))
        (α : Ops {σ = σ} X) (sat : _) (ρ : (v : V) → X (vs v)) (v : V)
      → rec isSetX α sat ρ (gen v) ≡ ρ v

    recOp : ∀ {ℓX} {X : S → Type ℓX} (isSetX : (s : S) → isSet (X s))
        (α : Ops {σ = σ} X) (sat : _) (ρ : (v : V) → X (vs v))
        (o : σ .ops) (ms : (a : arities σ o) → Carrier (σ .sortOf o a))
      → rec isSetX α sat ρ (op o ms) ≡ α o (λ a → rec isSetX α sat ρ (ms a))

    recUniq : ∀ {ℓX} {X : S → Type ℓX} (isSetX : (s : S) → isSet (X s))
        (α : Ops {σ = σ} X) (sat : _) (ρ : (v : V) → X (vs v))
        (f : (s : S) → Carrier s → X s)
      → ((o : σ .ops) (ms : (a : arities σ o) → Carrier (σ .sortOf o a))
          → f (σ .resultSort o) (op o ms) ≡ α o (λ a → f (σ .sortOf o a) (ms a)))
      → ((v : V) → f (vs v) (gen v) ≡ ρ v)
      → {s : S} (m : Carrier s) → f s m ≡ rec isSetX α sat ρ m

open FreePresentation public
