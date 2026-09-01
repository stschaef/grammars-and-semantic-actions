{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- Monoid theory freely extended by equations over the same signature.
   NOT `Instances/Monoid`: `MonEqns = MonPlusEqns ⊥` would be circular, and
   here nothing computes (`closingPresentation`), so transport is the only
   option. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Equality as Eq
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)
open SortedSig
open SortedEqns
open import Theory.Instances.Monoid.Base
module Theory.Instances.Monoid.Extension
  {ℓE} (Ext : Type ℓE) (extVars : Ext → ℕ)
  (extLhs extRhs : (e : Ext) → Tm MonSig (Fin (extVars e)) (λ _ → tt) tt)
  (El : Type ℓ-zero)
  where

open import Cubical.Data.Sigma

data MonPlusEqn : Type ℓE where
  mon : MonEqn → MonPlusEqn
  ext : Ext → MonPlusEqn

MonPlusEqns : SortedEqns MonSig ℓE
MonPlusEqns .eqns = MonPlusEqn
MonPlusEqns .eqnSort _ = tt
MonPlusEqns .varCount (mon e) = MonEqns .varCount e
MonPlusEqns .varCount (ext e) = extVars e
MonPlusEqns .varSort _ _ = tt
MonPlusEqns .lhs (mon e) = MonEqns .lhs e
MonPlusEqns .lhs (ext e) = extLhs e
MonPlusEqns .rhs (mon e) = MonEqns .rhs e
MonPlusEqns .rhs (ext e) = extRhs e

open import Theory.Free.Closing MonPlusEqns El (λ _ → tt)
  using (closingPresentation) public
open import Theory.Base MonPlusEqns El (λ _ → tt) closingPresentation public
open import Theory.Type.Lift.Base MonPlusEqns El (λ _ → tt)
  closingPresentation public
open import Theory.Type.Sum.Base MonPlusEqns El (λ _ → tt)
  closingPresentation public
open import Theory.Type.Operation.Base MonPlusEqns El (λ _ → tt)
  closingPresentation public
open import Theory.Type.Inductive.Base MonPlusEqns El (λ _ → tt)
  closingPresentation public
open import Theory.Type.Product.Binary.Base MonPlusEqns El (λ _ → tt)
  closingPresentation public
open import Theory.Type.Function.Base MonPlusEqns El (λ _ → tt)
  closingPresentation public
open import Theory.Type.Representable.Base MonPlusEqns El (λ _ → tt)
  closingPresentation public

private variable ℓA ℓB ℓC ℓA' ℓB' : Level

Carrier : Type ℓM
Carrier = ↓M tt

elem : TheoryTy ℓM tt
elem = ⊕[ c ∈ El ] ⌈ ⌈gen c ⌉ ⌉

ε⊗ : TheoryTy ℓM tt
ε⊗ = ⊗[ ε· ][ (λ ()) ] tt*

infixr 20 _⊗ₑ_
_⊗ₑ_ : TheoryTy ℓA tt → TheoryTy ℓB tt → TheoryTy _ tt
_⊗ₑ_ {ℓA = ℓA} {ℓB = ℓB} A B = ⊗[ _⊙_ ][ two ℓA ℓB ] (A , B , tt*)

⊗ₑmap : {A : TheoryTy ℓA tt} {A' : TheoryTy ℓA' tt}
        {B : TheoryTy ℓB tt} {B' : TheoryTy ℓB' tt}
  → A ⊢ A' → B ⊢ B' → A ⊗ₑ B ⊢ A' ⊗ₑ B'
⊗ₑmap {ℓA = ℓA} {ℓA' = ℓA'} {ℓB = ℓB} {ℓB' = ℓB'} {A} {A'} {B} {B'} f g =
  ⊗map[ _⊙_ ][ two ℓA ℓB ] (two ℓA' ℓB')
    {As = A , B , tt*} {Bs = A' , B' , tt*}
    (λ where zero → f
             (suc zero) → g)

-- equations read off the presentation, `two`/`three` tuples η-expanded

infixr 20 _⊙ᵖ_
_⊙ᵖ_ : Carrier → Carrier → Carrier
a ⊙ᵖ b = op _⊙_ (two a b)

εᵖ : Carrier
εᵖ = op ε· λ ()

opaque
  ⊙-unitL : (a : Carrier) → εᵖ ⊙ᵖ a ≡ a
  ⊙-unitL a =
    cong (op _⊙_) (funExt (λ where
      zero → cong (op ε·) (funExt λ ())
      (suc zero) → refl))
    ∙ M .snd .snd (mon unitL) (λ _ → a)

opaque
  ⊙-unitR : (a : Carrier) → a ⊙ᵖ εᵖ ≡ a
  ⊙-unitR a =
    cong (op _⊙_) (funExt (λ where
      zero → refl
      (suc zero) → cong (op ε·) (funExt λ ())))
    ∙ M .snd .snd (mon unitR) (λ _ → a)

opaque
  ⊙-assoc : (a b c : Carrier) → (a ⊙ᵖ b) ⊙ᵖ c ≡ a ⊙ᵖ (b ⊙ᵖ c)
  ⊙-assoc a b c =
    cong (op _⊙_) (funExt (λ where
      zero → cong (op _⊙_) (funExt (two refl refl))
      (suc zero) → refl))
    ∙ M .snd .snd (mon assoc) (three a b c)
    ∙ cong (op _⊙_) (funExt (λ where
        zero → refl
        (suc zero) → cong (op _⊙_) (funExt (two refl refl))))

private
  ⊙η : (f : Fin 2 → Carrier) → op _⊙_ f ≡ f zero ⊙ᵖ f (suc zero)
  ⊙η f = cong (op _⊙_) (funExt (two refl refl))

-- Associativity of `⊗ₑ`, by transport along `assoc`; the glue converts
-- between the two-slot tuple and the term of the equation.

private
  toTmA : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
    → (A ⊗ₑ B) ⊗ₑ C
    ⊢ ⟪ (var zero · var (suc zero)) · var (suc (suc zero)) ⟫[ three ℓA ℓB ℓC ]
        (A , B , C , tt*)
  toTmA m (ms , e , (inner , z , tt*)) =
    three (inner .fst zero) (inner .fst (suc zero)) (ms (suc zero))
    , Eq.pathToEq
        (cong (op _⊙_) (funExt (λ where
           zero → cong (op _⊙_) (funExt (two refl refl))
                  ∙ Eq.eqToPath (inner .snd .fst)
           (suc zero) → refl))
         ∙ Eq.eqToPath e)
    , (inner .snd .snd .fst , inner .snd .snd .snd .fst , z , tt*)

  fromTmA : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
    → ⟪ var zero · (var (suc zero) · var (suc (suc zero))) ⟫[ three ℓA ℓB ℓC ]
        (A , B , C , tt*)
    ⊢ A ⊗ₑ (B ⊗ₑ C)
  fromTmA m (ρ , e , (x , y , z , tt*)) =
    (λ b → eval ρ (two (var zero) (var (suc zero) · var (suc (suc zero))) b))
    , e
    , (x
      , ((λ b → eval ρ (two (var (suc zero)) (var (suc (suc zero))) b))
        , Eq.refl
        , (y , z , tt*))
      , tt*)

⊗ₑ-assoc : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → (A ⊗ₑ B) ⊗ₑ C ⊢ A ⊗ₑ (B ⊗ₑ C)
⊗ₑ-assoc {ℓA = ℓA} {ℓB = ℓB} {ℓC = ℓC} {A = A} {B = B} {C = C} =
  fromTmA {A = A} {B = B} {C = C}
    ∘⊢ eqn→fun (mon assoc) (three ℓA ℓB ℓC) (A , B , C , tt*)
    ∘⊢ toTmA {A = A} {B = B} {C = C}

private
  toTmA⁻ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
    → A ⊗ₑ (B ⊗ₑ C)
    ⊢ ⟪ var zero · (var (suc zero) · var (suc (suc zero))) ⟫[ three ℓA ℓB ℓC ]
        (A , B , C , tt*)
  toTmA⁻ m (ms , e , (x , inner , tt*)) =
    three (ms zero) (inner .fst zero) (inner .fst (suc zero))
    , Eq.pathToEq
        (cong (op _⊙_) (funExt (λ where
           zero → refl
           (suc zero) → cong (op _⊙_) (funExt (two refl refl))
                        ∙ Eq.eqToPath (inner .snd .fst)))
         ∙ Eq.eqToPath e)
    , (x , inner .snd .snd .fst , inner .snd .snd .snd .fst , tt*)

  fromTmA⁻ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
    → ⟪ (var zero · var (suc zero)) · var (suc (suc zero)) ⟫[ three ℓA ℓB ℓC ]
        (A , B , C , tt*)
    ⊢ (A ⊗ₑ B) ⊗ₑ C
  fromTmA⁻ m (ρ , e , (x , y , z , tt*)) =
    (λ b → eval ρ (two (var zero · var (suc zero)) (var (suc (suc zero))) b))
    , e
    , ( ((λ b → eval ρ (two (var zero) (var (suc zero)) b))
        , Eq.refl
        , (x , y , tt*))
      , z , tt*)

⊗ₑ-assoc⁻ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → A ⊗ₑ (B ⊗ₑ C) ⊢ (A ⊗ₑ B) ⊗ₑ C
⊗ₑ-assoc⁻ {ℓA = ℓA} {ℓB = ℓB} {ℓC = ℓC} {A = A} {B = B} {C = C} =
  fromTmA⁻ {A = A} {B = B} {C = C}
    ∘⊢ eqn→inv (mon assoc) (three ℓA ℓB ℓC) (A , B , C , tt*)
    ∘⊢ toTmA⁻ {A = A} {B = B} {C = C}

⊗ᵘ→⊗ₑ : (P : Fin 2 → TheoryTy ℓA tt)
  → ⊗ᵘ[ _⊙_ ] P ⊢ P zero ⊗ₑ P (suc zero)
⊗ᵘ→⊗ₑ P m (ms , e , h) = ms , e , (h zero , h (suc zero) , tt*)

⊗ₑ→⊗ᵘ : (P : Fin 2 → TheoryTy ℓA tt)
  → P zero ⊗ₑ P (suc zero) ⊢ ⊗ᵘ[ _⊙_ ] P
⊗ₑ→⊗ᵘ P m (ms , e , (a , b , tt*)) = ms , e , two a b

ε⊗→⌈ε⌉ : ε⊗ ⊢ ⌈ εᵖ ⌉
ε⊗→⌈ε⌉ m (ms , e , tt*) = Eq.sym e Eq.∙ Eq.pathToEq (cong (op ε·) (funExt λ ()))

⌈ε⌉→ε⊗ : ⌈ εᵖ ⌉ ⊢ ε⊗
⌈ε⌉→ε⊗ m Eq.refl = (λ ()) , Eq.refl , tt*

⊗ₑ-unitL⁻ : {A : TheoryTy ℓA tt} → A ⊢ ε⊗ ⊗ₑ A
⊗ₑ-unitL⁻ m a =
  two εᵖ m , Eq.pathToEq (⊙-unitL m) , (((λ ()) , Eq.refl , tt*) , a , tt*)

⊗ₑ-unitR⁻ : {A : TheoryTy ℓA tt} → A ⊢ A ⊗ₑ ε⊗
⊗ₑ-unitR⁻ m a =
  two m εᵖ , Eq.pathToEq (⊙-unitR m) , (a , ((λ ()) , Eq.refl , tt*) , tt*)

⊗ₑ-unitL : {A : TheoryTy ℓA tt} → ε⊗ ⊗ₑ A ⊢ A
⊗ₑ-unitL {A = A} m (ms , e , (z , a , tt*)) = subst A path a
  where
  path : ms (suc zero) ≡ m
  path =
    sym (⊙-unitL (ms (suc zero)))
    ∙ cong (_⊙ᵖ ms (suc zero)) (sym (Eq.eqToPath (ε⊗→⌈ε⌉ (ms zero) z)))
    ∙ sym (⊙η ms)
    ∙ Eq.eqToPath e

⊗ₑ-unitR : {A : TheoryTy ℓA tt} → A ⊗ₑ ε⊗ ⊢ A
⊗ₑ-unitR {A = A} m (ms , e , (a , z , tt*)) = subst A path a
  where
  path : ms zero ≡ m
  path =
    sym (⊙-unitR (ms zero))
    ∙ cong (ms zero ⊙ᵖ_) (sym (Eq.eqToPath (ε⊗→⌈ε⌉ (ms (suc zero)) z)))
    ∙ sym (⊙η ms)
    ∙ Eq.eqToPath e

⊗ₑ-unitL⌈⌉ : {a : Carrier} → ε⊗ ⊗ₑ ⌈ a ⌉ ⊢ ⌈ a ⌉
⊗ₑ-unitL⌈⌉ m (ms , e , (z , w , tt*)) = Eq.pathToEq (sym path ∙ Eq.eqToPath w)
  where
  path : ms (suc zero) ≡ m
  path =
    sym (⊙-unitL (ms (suc zero)))
    ∙ cong (_⊙ᵖ ms (suc zero)) (sym (Eq.eqToPath (ε⊗→⌈ε⌉ (ms zero) z)))
    ∙ sym (⊙η ms)
    ∙ Eq.eqToPath e

-- residual: right adjoint to `_⊗ₑ_` in its second argument

infixr 12 _⊸ₑ_
_⊸ₑ_ : TheoryTy ℓA tt → TheoryTy ℓB tt → TheoryTy _ tt
(A ⊸ₑ B) m = (ms : Fin 2 → Carrier) → ms zero Eq.≡ m
           → (z : Carrier) → op _⊙_ ms Eq.≡ z → A (ms (suc zero)) → B z

⊸ₑ-intro : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → A ⊗ₑ B ⊢ C → A ⊢ B ⊸ₑ C
⊸ₑ-intro f m a ms Eq.refl z q b = f z (ms , q , (a , b , tt*))

⊸ₑ-app : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} → (A ⊸ₑ B) ⊗ₑ A ⊢ B
⊸ₑ-app m (ms , e , (f , a , tt*)) = f ms Eq.refl m e a

⊸ₑ-intro⁻ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → A ⊢ B ⊸ₑ C → A ⊗ₑ B ⊢ C
⊸ₑ-intro⁻ {B = B} {C = C} f =
  ⊸ₑ-app {A = B} {B = C} ∘⊢ ⊗ₑmap f (id⊢ {A = B})

K : ∀ {ℓ} → Type ℓ → TheoryTy ℓ tt
K P _ = P

Kmap : ∀ {ℓP ℓQ} {P : Type ℓP} {Q : Type ℓQ} → (P → Q) → K P ⊢ K Q
Kmap f _ = f

K-intro : ∀ {ℓP} {P : Type ℓP} {A : TheoryTy ℓA tt} → P → A ⊢ K P
K-intro p _ _ = p

K-elim : ∀ {ℓP} {P : Type ℓP} {A : TheoryTy ℓA tt} {C : TheoryTy ℓB tt}
  → (P → A ⊢ C) → K P & A ⊢ C
K-elim f m (p , a) = f p m a

K-out : ∀ {ℓP} {P : Type ℓP} {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → (K P & A) ⊗ₑ B ⊢ K P & (A ⊗ₑ B)
K-out m (ms , e , ((p , a) , b , tt*)) = p , (ms , e , (a , b , tt*))

K-⊗ₑ₁ : ∀ {ℓP} {P : Type ℓP} {B : TheoryTy ℓB tt} → K P ⊗ₑ B ⊢ K P
K-⊗ₑ₁ m (ms , e , (p , b , tt*)) = p

K-⊗ₑ₂ : ∀ {ℓP} {P : Type ℓP} {A : TheoryTy ℓA tt} → A ⊗ₑ K P ⊢ K P
K-⊗ₑ₂ m (ms , e , (a , p , tt*)) = p

⊗ₑ⊕ᴰ-dist : ∀ {ℓY} {Y : Type ℓY} {A : Y → TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → (⊕[ y ∈ Y ] A y) ⊗ₑ B ⊢ ⊕[ y ∈ Y ] (A y ⊗ₑ B)
⊗ₑ⊕ᴰ-dist m (ms , e , ((y , a) , b , tt*)) = y , (ms , e , (a , b , tt*))
