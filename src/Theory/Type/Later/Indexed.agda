-- Semantic reasoning about guarded recursion, sequestered behind a clean interface.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns

import Theory.Free.Base as FB
module Theory.Type.Later.Indexed
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sum using (inl)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Nat using (ℕ ; discreteℕ)
import Cubical.Data.Nat.Order as NO
open import Cubical.Data.Nat.WFOrder using (ℕWF)
open import Cubical.Induction.WellFounded
open import Cubical.Relation.Nullary.Base using (Dec)
open import Cubical.Relation.Nullary.Base using (Discrete)

open import Cubical.Categories.Direct.Base
open import Theory.Type.Later.Poset using (PosetDirect)
open import Cubical.Categories.Presheaf.StrictHom.Base using (pshhom)
import Cubical.Categories.Direct.StrictDownset as SD

open import Theory.Type.Later.Lex
open import Theory.Type.Later.Tag

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Top.Base σeq V vs 𝒫
open import Theory.Type.Lift.Base σeq V vs 𝒫
open import Theory.Type.Product.Binary.Base σeq V vs 𝒫
  using (_&_ ; _,&_ ; _,&p_ ; π₁ ; π₂)
open import Theory.Type.Product.Base σeq V vs 𝒫 using (&ᴰ)

private variable ℓA ℓB ℓX ℓY ℓ< : Level

module _ {X : Type ℓX} (xs : X → S) where

  ℓIPt : Level
  ℓIPt = ℓ-max ℓX ℓM

  IPt : Type ℓIPt
  IPt = Σ[ x ∈ X ] ↓M (xs x)

  isSetIPt : isSet X → isSet IPt
  isSetIPt isSetX = isSetΣ isSetX λ x → M .fst (xs x) .snd

  IFam : (ℓB : Level) → Type (ℓ-max ℓIPt (ℓ-suc ℓB))
  IFam ℓB = (x : X) → TheoryTy ℓB (xs x)

  record IPtOrder (ℓ< : Level) : Type (ℓ-suc (ℓ-max ℓIPt ℓ<)) where
    field
      isSetIndex : isSet X
      _<_ : IPt → IPt → Type (ℓ-max ℓIPt ℓ<)
      isProp< : ∀ p q → isProp (p < q)
      trans< : ∀ {p q r} → p < q → q < r → p < r
      wf< : WellFounded _<_

    toWFOrder : WFOrder ℓIPt (ℓ-max ℓIPt ℓ<)
    toWFOrder = record
      { D = IPt ; isSetD = isSetIPt isSetIndex ; _<_ = _<_
      ; isProp< = isProp< ; trans< = trans< ; wf< = wf< }

  module _ (isSetX : isSet X) {ℓW} (W : WFOrder ℓW ℓ<)
    (meas : IPt → WFOrder.D W) where
    private
      module W = WFOrder W

      _<r_ : IPt → IPt → Type (ℓ-max ℓIPt ℓ<)
      p <r q = Lift ℓIPt (meas p W.< meas q)

      Wpb : WFOrder ℓIPt ℓ<
      Wpb = pullbackWFOrder W (isSetIPt isSetX) meas

      accLift : ∀ p → Acc (WFOrder._<_ Wpb) p → Acc _<r_ p
      accLift p (acc r) = acc λ q lt → accLift q (r q (lt .lower))

    irankOrder : IPtOrder ℓ<
    irankOrder .IPtOrder.isSetIndex = isSetX
    irankOrder .IPtOrder._<_ = _<r_
    irankOrder .IPtOrder.isProp< p q =
      isOfHLevelLift 1 (W.isProp< (meas p) (meas q))
    irankOrder .IPtOrder.trans< lt lt' = lift (W.trans< (lt .lower) (lt' .lower))
    irankOrder .IPtOrder.wf< p = accLift p (WFOrder.wf< Wpb p)

  LexStep : (size : (x : X) → ↓M (xs x) → ℕ) (rank : X → ℕ)
          → IPt → IPt → Type ℓ-zero
  LexStep size rank p q =
    _<lex_ ℕWF ℕWF (size (p .fst) (p .snd) , rank (p .fst))
                   (size (q .fst) (q .snd) , rank (q .fst))

  decLexStep : (size : (x : X) → ↓M (xs x) → ℕ) (rank : X → ℕ)
             → ∀ p q → Dec (LexStep size rank p q)
  decLexStep size rank p q = dec<lex ℕWF ℕWF discreteℕ
    (λ a a' → NO.≤Dec (ℕ.suc a) a') (λ b b' → NO.≤Dec (ℕ.suc b) b') _ _

  module _ (isSetX : isSet X) (size : (x : X) → ↓M (xs x) → ℕ)
    (rank : X → ℕ) where
    ilexOrder : IPtOrder ℓ-zero
    ilexOrder = irankOrder isSetX (lexWFOrder ℕWF ℕWF)
      λ p → size (p .fst) (p .snd) , rank (p .fst)

  module _ {ℓW ℓW<} (W : WFOrder ℓW ℓW<)
    (inp : (x : X) → ↓M (xs x) → WFOrder.D W) (rank : X → ℕ) where
    private
      module W = WFOrder W

      imeas : IPt → W.D × ℕ
      imeas p = inp (p .fst) (p .snd) , rank (p .fst)

    SuffixStep : IPt → IPt → Type (ℓ-max ℓW< ℓW)
    SuffixStep p q = _<lex_ W ℕWF (imeas p) (imeas q)

    decSuffixStep : Discrete W.D → (∀ a a' → Dec (a W.< a'))
                  → ∀ p q → Dec (SuffixStep p q)
    decSuffixStep dD dW p q =
      dec<lex W ℕWF dD dW (λ b b' → NO.≤Dec (ℕ.suc b) b') _ _

    isuffixOrder : isSet X → IPtOrder (ℓ-max ℓW< ℓW)
    isuffixOrder isSetX = irankOrder isSetX (lexWFOrder W ℕWF) imeas

  module GuardedIndexed (O : IPtOrder ℓ<) where
    open IPtOrder O public using (_<_)

    private
      dir = PosetDirect (IPtOrder.toWFOrder O)
      module Wo = WFOrder (IPtOrder.toWFOrder O)

    ℓ▷ : Level → Level
    ℓ▷ ℓA = ℓ-max ℓA (ℓ-max ℓIPt ℓ<)

    module Fam▷ (A : IFam ℓA) (isSetA : ∀ x m → isSet (A x m)) where
      private
        Â : IPt → hSet (ℓ▷ ℓA)
        Â p = LiftTheoryTy (ℓ-max ℓIPt ℓ<) (A (p .fst)) (p .snd)
          , isOfHLevelLift 2 (isSetA (p .fst) (p .snd))

      ▷ : IFam (ℓ▷ ℓA)
      ▷ x m = ⟨ SD.▷Fam dir {ℓF = ℓA} Â (x , m) ⟩

      Point : Type _
      Point = ∀ x → ⊤Ty ⊢ A x

      private
        ext : Point → ∀ p → ⟨ Â p ⟩
        ext t p = lift (t (p .fst) (p .snd) tt)

        int : (∀ p → ⟨ Â p ⟩) → Point
        int t x m _ = t (x , m) .lower

      next⊤ : Point → ∀ x → ⊤Ty ⊢ ▷ x
      next⊤ t x m _ = SD.nextFam dir {ℓF = ℓA} Â (ext t) (x , m)

      ▷app : ∀ {x m x' m'} → (x' , m') < (x , m) → ▷ x m → A x' m'
      ▷app lt β = SD.▷FamApp dir {ℓF = ℓA} Â β (inl lt) lt .lower

      isSet▷ : ∀ x m → isSet (▷ x m)
      isSet▷ x m = str (SD.▷Fam dir {ℓF = ℓA} Â (x , m))

      ▷intro : ∀ {x m} → (∀ x' m' → (x' , m') < (x , m) → A x' m') → ▷ x m
      ▷intro t = pshhom
        (λ q lt r h → lift (t (r .fst) (r .snd) (Wo.≤-<-trans h (lt .snd))))
        (λ q q' f p' p e → funExt λ r → funExt λ h →
          cong lift (cong (t (r .fst) (r .snd)) (IPtOrder.isProp< O _ _ _ _)))

      module _ (φ : ∀ x → ▷ x ⊢ A x) where
        private
          φ̂ : ∀ p → ⟨ SD.▷Fam dir {ℓF = ℓA} Â p ⟩ → ⟨ Â p ⟩
          φ̂ p β = lift (φ (p .fst) (p .snd) β)

        löb : Point
        löb = int (SD.löbFam dir {ℓF = ℓA} Â φ̂)

        löb-unfold : ∀ x → löb x ≡ φ x ∘⊢ next⊤ löb x
        löb-unfold x = funExt λ m → funExt λ _ →
          cong lower (SD.löbFam-unfold dir {ℓF = ℓA} Â φ̂ (x , m))

        löb-uniq : (t : Point) → (∀ x → t x ≡ φ x ∘⊢ next⊤ t x) → t ≡ löb
        löb-uniq t teq =
          cong int (SD.löbFam-uniq-unfold dir {ℓF = ℓA} Â φ̂ (ext t)
            λ p → cong lift (funExt⁻ (funExt⁻ (teq (p .fst)) (p .snd)) tt))

    SetFam : (ℓA : Level) → Type _
    SetFam ℓA = Σ[ A ∈ IFam ℓA ] (∀ x m → isSet (A x m))

    _&Set_ : SetFam ℓA → SetFam ℓB → SetFam (ℓ-max ℓA ℓB)
    (A &Set B) = (λ x → A .fst x & B .fst x)
               , λ x m → isSet× (A .snd x m) (B .snd x m)

    module _ (A : SetFam ℓA) where
      ▷ : IFam (ℓ▷ ℓA)
      ▷ = Fam▷.▷ (A .fst) (A .snd)

      isSet▷ : ∀ x m → isSet (▷ x m)
      isSet▷ = Fam▷.isSet▷ (A .fst) (A .snd)

      ▷Set : SetFam (ℓ▷ ℓA)
      ▷Set = ▷ , isSet▷

      ▷app : ∀ {x m x' m'} → (x' , m') < (x , m) → ▷ x m → A .fst x' m'
      ▷app = Fam▷.▷app (A .fst) (A .snd)

      ▷next : (∀ x → ⊤Ty ⊢ A .fst x) → ∀ x → ⊤Ty ⊢ ▷ x
      ▷next = Fam▷.next⊤ (A .fst) (A .snd)

    ▷δ : (A : SetFam ℓA) → ∀ x → ▷ A x ⊢ ▷ (▷Set A) x
    ▷δ A x m β = Fam▷.▷intro (▷ A) (isSet▷ A) λ x' m' lt →
      Fam▷.▷intro (A .fst) (A .snd) λ x'' m'' lt' →
        ▷app A (IPtOrder.trans< O lt' lt) β

    module _ {A : SetFam ℓA} {B : SetFam ℓB} where
      ▷map : (∀ x → A .fst x ⊢ B .fst x) → ∀ x → ▷ A x ⊢ ▷ B x
      ▷map f x m β = Fam▷.▷intro (B .fst) (B .snd) λ x' m' lt →
        f x' m' (▷app A lt β)

      ▷lax : ∀ x → ▷ A x & ▷ B x ⊢ ▷ (A &Set B) x
      ▷lax x m (α , β) =
        Fam▷.▷intro ((A &Set B) .fst) ((A &Set B) .snd) λ x' m' lt →
          ▷app A lt α , ▷app B lt β

    &SetFam : {Y : Type ℓY} → (Y → SetFam ℓA) → SetFam (ℓ-max ℓY ℓA)
    &SetFam {Y = Y} A =
      (λ x → &ᴰ Y (λ y → A y .fst x)) , λ x m → isSetΠ λ y → A y .snd x m

    ▷laxᴰ : {Y : Type ℓY} (A : Y → SetFam ℓA) → ∀ x
      → &ᴰ Y (λ y → ▷ (A y) x) ⊢ ▷ (&SetFam A) x
    ▷laxᴰ A x m f =
      Fam▷.▷intro (&SetFam A .fst) (&SetFam A .snd) λ x' m' lt y →
        ▷app (A y) lt (f y)

    □Set : SetFam ℓA → SetFam (ℓ▷ ℓA)
    □Set A = A &Set ▷Set A

    ▷? : ParserTag → SetFam ℓA → SetFam (ℓ▷ ℓA)
    ▷? ⟨▷⟩ = ▷Set
    ▷? ⟨□⟩ = □Set

    □here : (A : SetFam ℓA) → ∀ x → □Set A .fst x ⊢ A .fst x
    □here A x = π₁

    ▷?wk : {t : ParserTag} (A : SetFam ℓA) → ∀ x → □Set A .fst x ⊢ ▷? t A .fst x
    ▷?wk {t = ⟨▷⟩} A x = π₂
    ▷?wk {t = ⟨□⟩} A x = id⊢

    module _ {A : SetFam ℓA} {B : SetFam ℓB} where
      ▷?map : {t : ParserTag} → (∀ x → A .fst x ⊢ B .fst x)
        → ∀ x → ▷? t A .fst x ⊢ ▷? t B .fst x
      ▷?map {t = ⟨▷⟩} f = ▷map {A = A} {B = B} f
      ▷?map {t = ⟨□⟩} f x = f x ,&p ▷map {A = A} {B = B} f x

      ▷?lax : {t : ParserTag} → ∀ x
        → ▷? t A .fst x & ▷? t B .fst x ⊢ ▷? t (A &Set B) .fst x
      ▷?lax {t = ⟨▷⟩} = ▷lax {A = A} {B = B}
      ▷?lax {t = ⟨□⟩} x =
        (π₁ ,&p π₁) ,& (▷lax {A = A} {B = B} x ∘⊢ (π₂ ,&p π₂))

      ▷□ : (∀ x → ▷ A x ⊢ B .fst x) → ∀ x → ▷ A x ⊢ □Set B .fst x
      ▷□ f x = f x ,& (▷map {A = ▷Set A} {B = B} f x ∘⊢ ▷δ A x)

    ▷?next : {t : ParserTag} (A : SetFam ℓA) → (∀ x → ⊤Ty ⊢ A .fst x)
      → ∀ x → ⊤Ty ⊢ ▷? t A .fst x
    ▷?next {t = ⟨▷⟩} A f = ▷next A f
    ▷?next {t = ⟨□⟩} A f x = f x ,& ▷next A f x

    ▷?laxᴰ : {t : ParserTag} {Y : Type ℓY} (A : Y → SetFam ℓA) → ∀ x
      → &ᴰ Y (λ y → ▷? t (A y) .fst x) ⊢ ▷? t (&SetFam A) .fst x
    ▷?laxᴰ {t = ⟨▷⟩} A x = ▷laxᴰ A x
    ▷?laxᴰ {t = ⟨□⟩} A x m f = (λ y → f y .fst) , ▷laxᴰ A x m (λ y → f y .snd)
