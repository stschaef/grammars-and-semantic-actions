{- Every bag is empty or a generator times a rest -- truncated, because on
   the quotient the choice of which generator is not determined: `comm`
   identifies the two decompositions of `a ⊙ b`.  With the truncation the
   total space IS a model, so this is again just a fold. -}
{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
import Cubical.Algebra.Theory.Finitary.Free.Closing as Cl
import Cubical.Data.Equality as Eq
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open SortedSig
open SortedEqns
module Theory.Instances.Bags.Generation (El : Type ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.PropositionalTruncation as PT
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Bags.Base El

View : Bag → Type ℓM
View m = (m ≡ εᵖ) ⊎ (Σ[ y ∈ El ] Σ[ rest ∈ Bag ] (⌈gen y ⌉ ⊙ᵖ rest ≡ m))

private
  T : Sorts → Type ℓM
  T _ = Σ[ m ∈ Bag ] ∥ View m ∥₁

  isSetT : ∀ s → isSet (T s)
  isSetT _ = isSetΣ (M .fst tt .snd) λ _ → isProp→isSet squash₁

  -- combining two views: whichever side offers a generator gives one
  joinView : (a b : Bag) → View a → View b → View (a ⊙ᵖ b)
  joinView a b (inl p) (inl q) =
    inl (cong (_⊙ᵖ b) p ∙ cong (εᵖ ⊙ᵖ_) q ∙ ⊙-unitL εᵖ)
  joinView a b (inl p) (inr (y , rest , q)) =
    inr (y , rest
      , sym (⊙-unitL (⌈gen y ⌉ ⊙ᵖ rest))
        ∙ (λ i → p (~ i) ⊙ᵖ q i))
  joinView a b (inr (y , rest , q)) _ =
    inr (y , rest ⊙ᵖ b
      , sym (⊙-assoc ⌈gen y ⌉ rest b) ∙ cong (_⊙ᵖ b) q)

  Tops : Ops {σ = MonSig} T
  Tops ε· f = εᵖ , ∣ inl refl ∣₁
  Tops _⊙_ f =
    f zero .fst ⊙ᵖ f (suc zero) .fst
    , PT.rec2 squash₁
        (λ v w → ∣ joinView (f zero .fst) (f (suc zero) .fst) v w ∣₁)
        (f zero .snd) (f (suc zero) .snd)

  TSat : (e : BagEqns .eqns)
         (ρ : (w : vars BagEqns e) → T (BagEqns .varSort e w))
       → TmRec T Tops ρ (BagEqns .lhs e) ≡ TmRec T Tops ρ (BagEqns .rhs e)
  TSat e ρ =
    Σ≡Prop (λ _ → squash₁) (fstPath e ρ)
    where
    fstPath : (e : BagEqns .eqns)
              (ρ : (w : vars BagEqns e) → T (BagEqns .varSort e w))
            → TmRec T Tops ρ (BagEqns .lhs e) .fst
            ≡ TmRec T Tops ρ (BagEqns .rhs e) .fst
    fstPath (mon assoc) ρ = ⊙-assoc (ρ zero .fst) (ρ (suc zero) .fst) (ρ (suc (suc zero)) .fst)
    fstPath (mon unitL) ρ = ⊙-unitL (ρ zero .fst)
    fstPath (mon unitR) ρ = ⊙-unitR (ρ zero .fst)
    fstPath (ext comm) ρ = ⊙-comm (ρ zero .fst) (ρ (suc zero) .fst)

  fold : Bag → T tt
  fold = Cl.rec BagEqns isSetT Tops TSat λ y → ⌈gen y ⌉ , ∣ inr (y , εᵖ , ⊙-unitR ⌈gen y ⌉) ∣₁

  -- the fold puts every bag back where it started
  fold-fst : (m : Bag) → fold m .fst ≡ m
  fold-fst m =
    (Cl.recUniq BagEqns (λ s → M .fst s .snd) op (M .snd .snd)
          (λ y → ⌈gen y ⌉) (λ _ z → fold z .fst)
          (λ where
            ε· u y eq → cong (λ z → fold z .fst) eq
                        ∙ cong (op ε·) (funExt λ ())
            _⊙_ u y eq → cong (λ z → fold z .fst) eq
                        ∙ cong (op _⊙_) (funExt λ where
                            zero → refl
                            (suc zero) → refl))
          (λ _ → refl) m)
    ∙ sym (Cl.recUniq BagEqns (λ s → M .fst s .snd) op (M .snd .snd)
             (λ y → ⌈gen y ⌉) (λ _ m → m) (λ o x y eq → eq) (λ _ → refl) m)

view : (m : Bag) → ∥ View m ∥₁
view m = subst (λ z → ∥ View z ∥₁) (fold-fst m) (fold m .snd)
