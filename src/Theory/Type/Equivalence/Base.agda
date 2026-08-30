-- Monos, retracts, and weak equivalence.  `_≅_` is already in `Theory.Base`
-- as the `WildCatIso` of `THEORYTY`; this is the rest of the vocabulary.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Embedding
open import Cubical.Algebra.Theory.Finitary
open import Cubical.WildCat.LocallySmall.Base
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Equivalence.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Sigma

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.HLevels σeq V vs 𝒫
open import Theory.Type.Representable.Base σeq V vs 𝒫

open Iso
open WildCatNotation
open WildCatIso

private variable ℓA ℓB ℓC ℓD : Level

-- A weak equivalence is maps in both directions and no laws: it says the two
-- types have the same points, not that they have the same parses.
record _≈_ {s : S} (A : TheoryTy ℓA s) (B : TheoryTy ℓB s)
  : Type (ℓ-max ℓM (ℓ-max ℓA ℓB)) where
  no-eta-equality
  constructor mkWeakEq
  field
    fun : A ⊢ B
    inv : B ⊢ A

infix 4 _≈_

open _≈_

id≈ : {s : S} {A : TheoryTy ℓA s} → A ≈ A
id≈ = mkWeakEq id⊢ id⊢

sym≈ : {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} → A ≈ B → B ≈ A
sym≈ e = mkWeakEq (e .inv) (e .fun)

_≈∙_ : {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {C : TheoryTy ℓC s}
  → A ≈ B → B ≈ C → A ≈ C
(e ≈∙ f) = mkWeakEq (f .fun ∘⊢ e .fun) (e .inv ∘⊢ f .inv)

infixr 10 _≈∙_

≅→≈ : {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} → A ≅ B → A ≈ B
≅→≈ e = mkWeakEq (e .fun) (e .inv)

-- A retract is a weak equivalence one of whose composites is the identity.
record _isRetractOf_ {s : S} (A : TheoryTy ℓA s) (B : TheoryTy ℓB s)
  : Type (ℓ-max ℓM (ℓ-max ℓA ℓB)) where
  no-eta-equality
  field
    weak : A ≈ B
    ret : weak .inv ∘⊢ weak .fun ≡ id⊢

infixr 10 _isRetractOf_

open _isRetractOf_

≅→isRetractOf : {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  → A ≅ B → A isRetractOf B
≅→isRetractOf e .weak = ≅→≈ e
≅→isRetractOf e .ret = e .ret

isMono : {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} → A ⊢ B → Typeω
isMono {s = s} {A = A} f =
  ∀ {ℓC} {C : TheoryTy ℓC s} (g h : C ⊢ A) → f ∘⊢ g ≡ f ∘⊢ h → g ≡ h

isMonoId : {s : S} {A : TheoryTy ℓA s} → isMono (id⊢ {A = A})
isMonoId g h p = p

Mono∘⊢ : {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {C : TheoryTy ℓC s}
  (f : A ⊢ B) (g : B ⊢ C) → isMono g → isMono f → isMono (g ∘⊢ f)
Mono∘⊢ f g mg mf h h' p = mf h h' (mg (f ∘⊢ h) (f ∘⊢ h') p)

hasRetraction→isMono : {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  (f : A ⊢ B) (g : B ⊢ A) → g ∘⊢ f ≡ id⊢ → isMono f
hasRetraction→isMono f g r h h' p =
  cong (_∘⊢ h) (sym r) ∙ cong (g ∘⊢_) p ∙ cong (_∘⊢ h') r

isRetractOf→isMono : {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  (r : A isRetractOf B) → isMono (r .weak .fun)
isRetractOf→isMono r =
  hasRetraction→isMono (r .weak .fun) (r .weak .inv) (r .ret)

≅→isMono : {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
  (e : A ≅ B) → isMono (e .fun)
≅→isMono e = hasRetraction→isMono (e .fun) (e .inv) (e .ret)

-- Yoneda turns a mono into an injection.
module _ {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {f : A ⊢ B} where
  private
    yo-nat : (m : ↓M s) (x : A m) → f ∘⊢ yoIso m .inv x ≡ yoIso m .inv (f m x)
    yo-nat m x = funExt λ m' → funExt λ where Eq.refl → refl

  isMono→injective : isMono f → (m : ↓M s) (x y : A m) → f m x ≡ f m y → x ≡ y
  isMono→injective mono m x y p =
    cong (yoIso m .fun) (mono (yoIso m .inv x) (yoIso m .inv y) q)
    where
    q : f ∘⊢ yoIso m .inv x ≡ f ∘⊢ yoIso m .inv y
    q = yo-nat m x ∙ cong (yoIso m .inv) p ∙ sym (yo-nat m y)

  isMono→hasPropFibers : isSetTheoryTy B → isMono f
    → (m : ↓M s) → hasPropFibers (f m)
  isMono→hasPropFibers isSetB mono m =
    injective→hasPropFibers (isSetB m) (isMono→injective mono m _ _)

  injective→isMono : ((m : ↓M s) (x y : A m) → f m x ≡ f m y → x ≡ y) → isMono f
  injective→isMono inj g h p =
    funExt λ m → funExt λ x →
      inj m (g m x) (h m x) (funExt⁻ (funExt⁻ p m) x)

-- Restated here because `THEORYTY`'s `⋆WildCatIso` is private to `Theory.Base`.
module _ {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {C : TheoryTy ℓC s}
  where
  _≅∙_ : A ≅ B → B ≅ C → A ≅ C
  (e ≅∙ f) .fun = f .fun ∘⊢ e .fun
  (e ≅∙ f) .inv = e .inv ∘⊢ f .inv
  (e ≅∙ f) .sec =
    cong (λ z → f .fun ∘⊢ z ∘⊢ f .inv) (e .sec) ∙ f .sec
  (e ≅∙ f) .ret =
    cong (λ z → e .inv ∘⊢ z ∘⊢ e .fun) (f .ret) ∙ e .ret

  infixr 10 _≅∙_

sym≅ : {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} → A ≅ B → B ≅ A
sym≅ e .fun = e .inv
sym≅ e .inv = e .fun
sym≅ e .sec = e .ret
sym≅ e .ret = e .sec

id≅ : {s : S} {A : TheoryTy ℓA s} → A ≅ A
id≅ .fun = id⊢
id≅ .inv = id⊢
id≅ .sec = refl
id≅ .ret = refl
