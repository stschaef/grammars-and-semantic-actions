{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Parsing with derivatives (Might-Darais-Spiewak): D = μ (λ x → δ (F x)).
   Known gap: no compaction, so the Adams-Hollenbeck-Might complexity
   bound does not apply. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Derivative.Parser
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.List using ([] ; _∷_ ; _++_)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)

open import Theory.Instances.Monoid.Combinator.Core Alphabet _≟_
open import Theory.Instances.Monoid.Regex.Derivative Alphabet _≟_ ℓ-zero
  using ( Dl-⊗-out⁺ ; Dl-⊗-in-l ; Dl-⊗-in-r⁺ )
open import Theory.Instances.Monoid.Derivative Alphabet isSetAlphabet
  using (Dl ; Dl-map ; Dl-string ; Dl-string-map)
open import Theory.Instances.Monoid.Derivative.General Alphabet isSetAlphabet
  using ( ∂[_]_ ; √[_]_ ; ∂-intro ; ∂-intro⁻ ; ∂-counit ; ∂⌈⌉→⊸ ; ⊸→∂⌈⌉
        ; ∂⌈⌉→Dl ; Dl→∂⌈⌉ )
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using ( ⊗ᵘ→⊗ ; ⊗→⊗ᵘ ; ⟦⊗e⟧ ; ⟦⊗e⟧⁻
        ; _⊸_ ; ⊸-lam ; ⊸-app ; ⊗ε-unit-r ; ⊗ε-unit-r⁻ )

private variable ℓA ℓX : Level

Nu : TheoryTy ℓA tt → TheoryTy _ tt
Nu A = A & εTy

module _ {X : Type ℓX} {xs : X → Unit}
  (F : (x : X) → Functor ℓA X xs tt) (c : Alphabet) where

  private
    ℓD : Level
    ℓD = ℓ-max (ℓF ℓA) ℓX

    Two : Type ℓX
    Two = Lift ℓX Bool

    A : (x : X) → TheoryTy ℓD tt
    A = μ F

    ⟦_⟧A : Functor ℓA X xs tt → TheoryTy ℓD tt
    ⟦ G ⟧A = ⟦ G ⟧TheoryTy A

  -- `Var x` names the *derivative* nonterminal; undifferentiated occurrences
  -- freeze as constants (μ F already built), so this δ iterates where
  -- `Derivative/OneStep`'s cannot.
  δ : Functor ℓA X xs tt → Functor ℓD X xs tt
  δ (k B) = k (LiftTheoryTy ℓD (Dl c B))
  δ (Var x) = Var x
  δ (⊕e Y G) = ⊕e Y λ y → δ (G y)
  δ (&e Y G) = &e Y λ y → δ (G y)
  δ (G &e2 G') = δ G &e2 δ G'
  δ (⊗e ε· G) = k (LiftTheoryTy ℓD (Dl c ⟦ ⊗e ε· G ⟧A))
  -- product rule; `Nu` keeps every null parse of an ambiguous left factor
  δ (⊗e _⊙_ G) = ⊕e Two λ where
    (lift true) →
      ⊗e _⊙_ (two (δ (G zero)) (k (LiftTheoryTy ℓD ⟦ G (suc zero) ⟧A)))
    (lift false) →
      ⊗e _⊙_ (two (k (LiftTheoryTy ℓD (Nu ⟦ G zero ⟧A))) (δ (G (suc zero))))

  -- The knot `OneStep.δ-sound` had to assume as `step`.
  D : (x : X) → TheoryTy (ℓ-max (ℓF ℓD) ℓX) tt
  D = μ λ x → δ (F x)

  -- Soundness is a plain fold: the recursive occurrence is `Var x`, so no
  -- `step` hypothesis.
  private
    sound' : (G : Functor ℓA X xs tt)
      → ⟦ δ G ⟧TheoryTy (λ y → Dl c (A y)) ⊢ Dl c ⟦ G ⟧A
    sound' (k B) = liftTy ∘⊢ lowerTy ∘⊢ lowerTy
    sound' (Var x) = liftTy ∘⊢ lowerTy
    sound' (⊕e Y G) = ⊕ᴰ-elim λ y → σ⊕ y ∘⊢ sound' (G y)
    sound' (&e Y G) = &ᴰ-intro λ y → sound' (G y) ∘⊢ π y
    sound' (G &e2 G') = sound' G ,&p sound' G'
    sound' (⊗e ε· G) = lowerTy ∘⊢ lowerTy
    sound' (⊗e _⊙_ G) = ⊕ᴰ-elim λ where
      (lift true) →
        Dl-map c (⊗→⊗ᵘ λ i → ⟦ G i ⟧A)
        ∘⊢ Dl-⊗-in-l c
        ∘⊢ (sound' (G zero) ,⊗ (lowerTy ∘⊢ lowerTy))
        ∘⊢ ⟦⊗e⟧ (δ (G zero)) (k (LiftTheoryTy ℓD ⟦ G (suc zero) ⟧A))
      (lift false) →
        Dl-map c (⊗→⊗ᵘ λ i → ⟦ G i ⟧A)
        ∘⊢ Dl-⊗-in-r⁺ c
        ∘⊢ ((lowerTy ∘⊢ lowerTy) ,⊗ sound' (G (suc zero)))
        ∘⊢ ⟦⊗e⟧ (k (LiftTheoryTy ℓD (Nu ⟦ G zero ⟧A))) (δ (G (suc zero)))

  sound : (x : X) → D x ⊢ Dl c (A x)
  sound = rec _ λ x → Dl-map c roll ∘⊢ sound' (F x)

  -- `Dl c (A x) ⊢ D x` is not a fold shape; `∂[ ⌈ c ⌉ ] ⊣ √[ ⌈ c ⌉ ]` turns
  -- it into `A x ⊢ √[ ⌈ c ⌉ ] (D x)`, which is.  The motive carries the
  -- original parse because δ freezes at `μ F`; `forget` projects back.
  private
    w : String
    w = ⌈gen c ⌉

    Mot : (x : X) → TheoryTy _ tt
    Mot x = A x & (√[ ⌈ w ⌉ ] (D x))

    forget : (G : Functor ℓA X xs tt) → ⟦ G ⟧TheoryTy Mot ⊢ ⟦ G ⟧A
    forget G = map G λ y → π₁

    comp' : (G : Functor ℓA X xs tt)
      → Dl c (⟦ G ⟧TheoryTy Mot) ⊢ ⟦ δ G ⟧TheoryTy D
    comp' (k B) = liftTy ∘⊢ liftTy ∘⊢ lowerTy
    comp' (Var x) =
      liftTy ∘⊢ ∂-counit ∘⊢ Dl→∂⌈⌉ w
      ∘⊢ Dl-map c (π₂ {A = A x} {B = √[ ⌈ w ⌉ ] (D x)})
      ∘⊢ lowerTy
    comp' (⊕e Y G) = ⊕ᴰ-elim λ y → σ⊕ y ∘⊢ comp' (G y)
    comp' (&e Y G) = &ᴰ-intro λ y → comp' (G y) ∘⊢ π y
    comp' (G &e2 G') = comp' G ,&p comp' G'
    comp' (⊗e ε· G) = liftTy ∘⊢ liftTy ∘⊢ Dl-map c (forget (⊗e ε· G))
    comp' (⊗e _⊙_ G) =
      ⊕-elim
        (σ⊕ (lift true)
         ∘⊢ ⟦⊗e⟧⁻ (δ (G zero)) (k (LiftTheoryTy ℓD ⟦ G (suc zero) ⟧A))
         ∘⊢ (comp' (G zero) ,⊗ (liftTy ∘⊢ liftTy ∘⊢ forget (G (suc zero)))))
        (σ⊕ (lift false)
         ∘⊢ ⟦⊗e⟧⁻ (k (LiftTheoryTy ℓD (Nu ⟦ G zero ⟧A))) (δ (G (suc zero)))
         ∘⊢ ((liftTy ∘⊢ liftTy ∘⊢ (forget (G zero) ,&p id⊢))
             ,⊗ comp' (G (suc zero))))
      ∘⊢ Dl-⊗-out⁺ c
      ∘⊢ Dl-map c (⊗ᵘ→⊗ λ i → ⟦ G i ⟧TheoryTy Mot)

    αc : (x : X) → ⟦ F x ⟧TheoryTy Mot ⊢ Mot x
    αc x = (roll ∘⊢ forget (F x))
        ,& ∂-intro (roll ∘⊢ comp' (F x) ∘⊢ ∂⌈⌉→Dl w)

  complete : (x : X) → Dl c (A x) ⊢ D x
  complete x = ∂-intro⁻ (π₂ ∘⊢ rec _ αc x) ∘⊢ Dl→∂⌈⌉ w

-- Iterating δ: each derivative freezes at the system the previous one built,
-- which `OneStep`'s δ cannot (`δ (dv x) = ⊥̂`).  Level grows ℓF per letter.
module _ {X : Type ℓX} {xs : X → Unit} where

  levOf : Level → String → Level
  levOf ℓ [] = ℓ
  levOf ℓ (c ∷ w) = levOf (ℓ-max (ℓF ℓ) ℓX) w

  -- `Dl-string (c ∷ w) = Dl-string w ∘ Dl c`: letters consumed left to right.
  δ* : {ℓ : Level} (w : String) (F : (x : X) → Functor ℓ X xs tt)
     → (x : X) → Functor (levOf ℓ w) X xs tt
  δ* [] F = F
  δ* (c ∷ w) F = δ* w λ x → δ F c (F x)

  D* : {ℓ : Level} (w : String) (F : (x : X) → Functor ℓ X xs tt)
     → (x : X) → TheoryTy _ tt
  D* w F = μ (δ* w F)

  sound* : {ℓ : Level} (w : String) (F : (x : X) → Functor ℓ X xs tt)
    → (x : X) → D* w F x ⊢ Dl-string w (μ F x)
  sound* [] F x = id⊢
  sound* (c ∷ w) F x =
    Dl-string-map w (sound F c x) ∘⊢ sound* w (λ y → δ F c (F y)) x

  complete* : {ℓ : Level} (w : String) (F : (x : X) → Functor ℓ X xs tt)
    → (x : X) → Dl-string w (μ F x) ⊢ D* w F x
  complete* [] F x = id⊢
  complete* (c ∷ w) F x =
    complete* w (λ y → δ F c (F y)) x ∘⊢ Dl-string-map w (complete F c x)

  fromNull : {ℓ : Level} (w : String) (F : (x : X) → Functor ℓ X xs tt)
    (x : X) → εTy ⊢ D* w F x → ⌈ w ⌉ ⊢ μ F x
  fromNull w F x nul =
    ⊸-app {A = ⌈ w ⌉} {C = μ F x}
    ∘⊢ (id⊢ ,⊗ (∂⌈⌉→⊸ w {B = μ F x} ∘⊢ Dl→∂⌈⌉ w ∘⊢ sound* w F x ∘⊢ nul))
    ∘⊢ ⊗ε-unit-r⁻

  toNull : {ℓ : Level} (w : String) (F : (x : X) → Functor ℓ X xs tt)
    (x : X) → ⌈ w ⌉ ⊢ μ F x → εTy ⊢ D* w F x
  toNull w F x p =
    complete* w F x ∘⊢ ∂⌈⌉→Dl w ∘⊢ ⊸→∂⌈⌉ w {B = μ F x}
    ∘⊢ ⊸-lam {A = ⌈ w ⌉} {B = εTy} {C = μ F x} (p ∘⊢ ⊗ε-unit-r)
