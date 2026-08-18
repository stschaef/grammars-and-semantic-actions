-- TODO how much of this actually used?
-- WARNING for now I have been treating this as a place to sequester the
-- semantic reasoning about guarded recursion so that importers of this
-- module can work with a clean interface
-- The implementation are subject to change per experiments w Cass
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Later.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sum using (inl)
open import Cubical.Induction.WellFounded
open import Cubical.Induction.WellFounded.More

open import Cubical.Categories.Direct.Base
open import Theory.Type.Later.Poset using (PosetDirect)
import Cubical.Categories.Direct.StrictDownset as SD

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Top.Base σeq V vs 𝒫
open import Theory.Type.Lift.Base σeq V vs 𝒫

private variable ℓA ℓW ℓ< : Level

ℓPt : Level
ℓPt = ℓ-max ℓS ℓM

Pt : Type ℓPt
Pt = Σ[ s ∈ S ] ↓M s

isSetPt : isSet S → isSet Pt
isSetPt isSetS = isSetΣ isSetS λ s → M .fst s .snd

Fam : (ℓA : Level) → Type (ℓ-max ℓPt (ℓ-suc ℓA))
Fam ℓA = (s : S) → TheoryTy ℓA s

record PtOrder (ℓ< : Level) : Type (ℓ-suc (ℓ-max ℓPt ℓ<)) where
  field
    isSetSort : isSet S
    _<_ : Pt → Pt → Type (ℓ-max ℓPt ℓ<)
    isProp< : ∀ p q → isProp (p < q)
    trans< : ∀ {p q r} → p < q → q < r → p < r
    wf< : WellFounded _<_

  toWFOrder : WFOrder ℓPt (ℓ-max ℓPt ℓ<)
  toWFOrder = record
    { D = Pt ; isSetD = isSetPt isSetSort ; _<_ = _<_
    ; isProp< = isProp< ; trans< = trans< ; wf< = wf< }

module _ (isSetS : isSet S) (W : WFOrder ℓW ℓ<) (rank : Pt → WFOrder.D W) where
  private
    module W = WFOrder W

    _<r_ : Pt → Pt → Type (ℓ-max ℓPt ℓ<)
    p <r q = Lift ℓPt (rank p W.< rank q)

    accLift : ∀ p → Acc (pullback< rank W._<_) p → Acc _<r_ p
    accLift p (acc r) = acc λ q lt → accLift q (r q (lt .lower))

  rankOrder : PtOrder ℓ<
  rankOrder .PtOrder.isSetSort = isSetS
  rankOrder .PtOrder._<_ = _<r_
  rankOrder .PtOrder.isProp< p q = isOfHLevelLift 1 (W.isProp< (rank p) (rank q))
  rankOrder .PtOrder.trans< lt lt' = lift (W.trans< (lt .lower) (lt' .lower))
  rankOrder .PtOrder.wf< p = accLift p (wfPullback rank W._<_ W.wf< p)

module Guarded {ℓ<} (O : PtOrder ℓ<) where
  open PtOrder O public using (_<_)

  private
    dir = PosetDirect (PtOrder.toWFOrder O)

  ℓ▷ : Level → Level
  ℓ▷ ℓA = ℓ-max ℓA (ℓ-max ℓPt ℓ<)

  module Fam▷ (A : Fam ℓA) (isSetA : ∀ s m → isSet (A s m)) where
    private
      Â : Pt → hSet (ℓ▷ ℓA)
      Â p = LiftTheoryTy (ℓ-max ℓPt ℓ<) (A (p .fst)) (p .snd)
          , isOfHLevelLift 2 (isSetA (p .fst) (p .snd))

    ▷ : Fam (ℓ▷ ℓA)
    ▷ s m = ⟨ SD.▷Fam dir {ℓF = ℓA} Â (s , m) ⟩

    Point : Type _
    Point = ∀ s → ⊤Ty ⊢ A s

    private
      ext : Point → ∀ p → ⟨ Â p ⟩
      ext t p = lift (t (p .fst) (p .snd) tt)

      int : (∀ p → ⟨ Â p ⟩) → Point
      int t s m _ = t (s , m) .lower

    next⊤ : Point → ∀ s → ⊤Ty ⊢ ▷ s
    next⊤ t s m _ = SD.nextFam dir {ℓF = ℓA} Â (ext t) (s , m)

    ▷app : ∀ {s m s' m'} → (s' , m') < (s , m) → ▷ s m → A s' m'
    ▷app lt β = SD.▷FamApp dir {ℓF = ℓA} Â β (inl lt) lt .lower

    module _ (φ : ∀ s → ▷ s ⊢ A s) where
      private
        φ̂ : ∀ p → ⟨ SD.▷Fam dir {ℓF = ℓA} Â p ⟩ → ⟨ Â p ⟩
        φ̂ p β = lift (φ (p .fst) (p .snd) β)

      löb : Point
      löb = int (SD.löbFam dir {ℓF = ℓA} Â φ̂)

      löb-unfold : ∀ s → löb s ≡ φ s ∘⊢ next⊤ löb s
      löb-unfold s = funExt λ m → funExt λ _ →
        cong lower (SD.löbFam-unfold dir {ℓF = ℓA} Â φ̂ (s , m))

      löb-uniq : (t : Point) → (∀ s → t s ≡ φ s ∘⊢ next⊤ t s) → t ≡ löb
      löb-uniq t teq =
        cong int (SD.löbFam-uniq-unfold dir {ℓF = ℓA} Â φ̂ (ext t)
          λ p → cong lift (funExt⁻ (funExt⁻ (teq (p .fst)) (p .snd)) tt))
