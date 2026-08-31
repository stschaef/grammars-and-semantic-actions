-- Disjointness, and the interaction of unambiguity with the two notions of
-- equivalence.  `disjoint A B` is the binary case of a `Cover`'s `disjoint`
-- field; it is stated separately because most clients only need two summands.
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.WildCat.LocallySmall.Base
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Unambiguity.Disjoint
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Sigma

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Top.Base σeq V vs 𝒫
open import Theory.Type.Bottom.Base σeq V vs 𝒫
open import Theory.Type.Product.Binary.Base σeq V vs 𝒫
open import Theory.Type.Sum.Binary.Base σeq V vs 𝒫
open import Theory.Type.Unambiguity.Base σeq V vs 𝒫
open import Theory.Type.Equivalence.Base σeq V vs 𝒫

open WildCatNotation
open WildCatIso
open _≈_
open _isRetractOf_

private
  variable
    ℓA ℓB ℓC ℓD : Level
    s : S
    A : TheoryTy ℓA s
    B : TheoryTy ℓB s
    C : TheoryTy ℓC s
    D : TheoryTy ℓD s

disjoint : {s : S} → TheoryTy ℓA s → TheoryTy ℓB s → Type (ℓ-max ℓM (ℓ-max ℓA ℓB))
disjoint A B = A & B ⊢ ⊥Ty

disjoint⊢ : disjoint A B → C ⊢ A → disjoint C B
disjoint⊢ dis f = dis ∘⊢ &par f id⊢

disjoint⊢2 : disjoint A B → C ⊢ A → D ⊢ B → disjoint C D
disjoint⊢2 dis f g = disjoint⊢ dis f ∘⊢ &par id⊢ g

disjoint≈ : disjoint A B → A ≈ C → disjoint C B
disjoint≈ dis e = disjoint⊢ dis (e .inv)

disjoint≅ : disjoint A B → A ≅ C → disjoint C B
disjoint≅ dis e = disjoint⊢ dis (e .inv)

disjoint≅2 : disjoint A B → A ≅ C → B ≅ D → disjoint C D
disjoint≅2 dis e f = disjoint≅ dis e ∘⊢ &par id⊢ (f .inv)

disjoint-sym : disjoint A B → disjoint B A
disjoint-sym dis = dis ∘⊢ &-swap

disjoint⊕l : disjoint (A ⊕ B) C → disjoint A C
disjoint⊕l dis = disjoint⊢ dis inl

disjoint⊕r : disjoint (A ⊕ B) C → disjoint B C
disjoint⊕r dis = disjoint⊢ dis inr

disjoint⊕ : disjoint A C → disjoint B C → disjoint (A ⊕ B) C
disjoint⊕ d d' = ⊕-elim& (d ∘⊢ &-swap) (d' ∘⊢ &-swap) ∘⊢ &-swap

-- Unambiguity from the diagonal.  These are the classical characterisations:
-- `A` is unambiguous iff the two projections out of `A & A` agree, iff the
-- diagonal is an isomorphism.
module _ {s : S} {A : TheoryTy ℓA s} where
  π≡→unambiguous : π₁ {A = A} {B = A} ≡ π₂ → unambiguous A
  π≡→unambiguous π≡ = subterminal→unambiguous λ e e' →
    sym (&-β₁ e e') ∙ cong (_∘⊢ (e ,& e')) π≡ ∙ &-β₂ e e'

  unambiguous→π≡ : unambiguous A → π₁ {A = A} {B = A} ≡ π₂
  unambiguous→π≡ u = unambiguous→subterminal u π₁ π₂

  -- `&-Δ` having a section already forces unambiguity: the section makes the
  -- two projections agree.
  Δsection→unambiguous : (g : (A & A) ⊢ A) → &-Δ ∘⊢ g ≡ id⊢ → unambiguous A
  Δsection→unambiguous g sec = π≡→unambiguous
    ( cong (π₁ ∘⊢_) (sym sec)
    ∙ cong (_∘⊢ g) (&-β₁ id⊢ id⊢)
    ∙ cong (_∘⊢ g) (sym (&-β₂ id⊢ id⊢))
    ∙ cong (π₂ ∘⊢_) sec )

  Δ≅→unambiguous : (Δ≅ : A ≅ (A & A)) → Δ≅ .fun ≡ &-Δ → unambiguous A
  Δ≅→unambiguous Δ≅ isΔ =
    Δsection→unambiguous (Δ≅ .inv) (cong (_∘⊢ Δ≅ .inv) (sym isΔ) ∙ Δ≅ .sec)

  unambiguous→Δ≅ : unambiguous A → A ≅ (A & A)
  unambiguous→Δ≅ u .fun = &-Δ
  unambiguous→Δ≅ u .inv = π₁
  unambiguous→Δ≅ u .sec = funExt λ m → funExt λ x → ΣPathP (refl , u m _ _)
  unambiguous→Δ≅ u .ret = refl

-- Transport of unambiguity, and the upgrade from a weak to a strong
-- equivalence that unambiguity licenses.
isUnambiguousRetract' : (f : A ⊢ B) (g : B ⊢ A) → g ∘⊢ f ≡ id⊢
  → unambiguous B → unambiguous A
isUnambiguousRetract' f g r uB = unambiguousRetract f g r uB

isUnambiguousRetract : A isRetractOf B → unambiguous B → unambiguous A
isUnambiguousRetract r =
  isUnambiguousRetract' (r .weak .fun) (r .weak .inv) (r .ret)

unambiguous≅ : A ≅ B → unambiguous A → unambiguous B
unambiguous≅ e = isUnambiguousRetract' (e .inv) (e .fun) (e .sec)

unambiguous→≅ : unambiguous A → unambiguous B → A ⊢ B → B ⊢ A → A ≅ B
unambiguous→≅ uA uB f g .fun = f
unambiguous→≅ uA uB f g .inv = g
unambiguous→≅ uA uB f g .sec = unambiguous→subterminal uB _ _
unambiguous→≅ uA uB f g .ret = unambiguous→subterminal uA _ _

unambiguousRetract'→≅ : (f : A ⊢ B) (g : B ⊢ A) → g ∘⊢ f ≡ id⊢
  → unambiguous B → A ≅ B
unambiguousRetract'→≅ f g r uB =
  unambiguous→≅ (isUnambiguousRetract' f g r uB) uB f g

unambiguousRetract→≅ : A isRetractOf B → unambiguous B → A ≅ B
unambiguousRetract→≅ r uB =
  unambiguous→≅ (isUnambiguousRetract r uB) uB (r .weak .fun) (r .weak .inv)

-- The point of `≈`: between unambiguous types it is already a `≅`.
≈→≅ : unambiguous A → unambiguous B → A ≈ B → A ≅ B
≈→≅ uA uB e = unambiguous→≅ uA uB (e .fun) (e .inv)

&⊤≅ : {s : S} {A : TheoryTy ℓA s} → A ≅ (A & ⊤Ty)
&⊤≅ .fun = id⊢ ,& ⊤Ty-intro
&⊤≅ .inv = π₁
&⊤≅ .sec = refl
&⊤≅ .ret = refl
