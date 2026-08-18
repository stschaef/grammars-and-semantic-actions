-- Theory of commutative monoids
-- TODO this could probably be cleaned up to share a lot of code
-- with the theory of monoids
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Equality as Eq
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open SortedSig
open SortedEqns
module Theory.Instances.Bags.Base (El : Type ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt ; tt*)

open import Theory.Instances.Monoid.Base

data BagEqn : Type ℓ-zero where
  assoc unitL unitR comm : BagEqn

BagEqns : SortedEqns MonSig ℓ-zero
BagEqns .eqns = BagEqn
BagEqns .eqnSort _ = tt
BagEqns .varCount assoc = 3
BagEqns .varCount unitL = 1
BagEqns .varCount unitR = 1
BagEqns .varCount comm = 2
BagEqns .varSort _ _ = tt
BagEqns .lhs assoc =
  (var zero · var (suc zero)) · var (suc (suc zero))
BagEqns .rhs assoc =
  var zero · (var (suc zero) · var (suc (suc zero)))
BagEqns .lhs unitL = ε · var zero
BagEqns .rhs unitL = var zero
BagEqns .lhs unitR = var zero · ε
BagEqns .rhs unitR = var zero
BagEqns .lhs comm = node _⊙_ var
BagEqns .rhs comm = node _⊙_ (λ b → var (swap b))

open import Theory.Free.Closing BagEqns El (λ _ → tt)
  using (closingPresentation)
open import Theory.Base BagEqns El (λ _ → tt) closingPresentation public
open import Theory.Type.Lift.Base BagEqns El (λ _ → tt) closingPresentation public
open import Theory.Type.Sum.Base BagEqns El (λ _ → tt) closingPresentation public
open import Theory.Type.Operation.Base BagEqns El (λ _ → tt) closingPresentation public
open import Theory.Type.Inductive.Base BagEqns El (λ _ → tt) closingPresentation public
open import Theory.Type.Product.Binary.Base BagEqns El (λ _ → tt) closingPresentation public
open import Theory.Type.Function.Base BagEqns El (λ _ → tt) closingPresentation public
open import Theory.Type.Representable.Base BagEqns El (λ _ → tt) closingPresentation public

private variable ℓA ℓB ℓC ℓA' ℓB' : Level

Bag : Type ℓM
Bag = ↓M tt

elem : TheoryTy ℓM tt
elem = ⊕[ c ∈ El ] ⌈ ⌈gen c ⌉ ⌉

εB : TheoryTy ℓM tt
εB = ⊗[ ε· ][ (λ ()) ] tt*

_⊎B_ : TheoryTy ℓA tt → TheoryTy ℓB tt → TheoryTy _ tt
_⊎B_ {ℓA = ℓA} {ℓB = ℓB} A B = ⊗[ _⊙_ ][ two ℓA ℓB ] (A , B , tt*)

fromTm : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → ⟪ node _⊙_ (λ b → var (swap b)) ⟫[ two ℓA ℓB ] (A , B , tt*) ⊢ B ⊎B A
fromTm m (ρ , e , (x , y , tt*)) = (λ b → ρ (swap b)) , e , (y , x , tt*)

⊎B-comm : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} → A ⊎B B ⊢ B ⊎B A
⊎B-comm {ℓA = ℓA} {ℓB = ℓB} {A = A} {B = B} =
  fromTm {A = A} {B = B} ∘⊢ eqn→fun comm (two ℓA ℓB) (A , B , tt*)

private
  toTmA : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
    → (A ⊎B B) ⊎B C
    ⊢ ⟪ (var zero · var (suc zero)) · var (suc (suc zero)) ⟫[ three ℓA ℓB ℓC ]
        (A , B , C , tt*)
  toTmA m (ms , e , (inner , z , tt*)) =
    ρ
    , Eq.pathToEq
        (cong (op _⊙_) (funExt (λ where
           zero → cong (op _⊙_) (funExt (λ where
                    zero → refl
                    (suc zero) → refl))
                  ∙ Eq.eqToPath (inner .snd .fst)
           (suc zero) → refl))
         ∙ Eq.eqToPath e)
    , (inner .snd .snd .fst , inner .snd .snd .snd .fst , z , tt*)
    where
    ρ : Fin 3 → Bag
    ρ = three (inner .fst zero) (inner .fst (suc zero)) (ms (suc zero))

  fromTmA : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
    → ⟪ var zero · (var (suc zero) · var (suc (suc zero))) ⟫[ three ℓA ℓB ℓC ]
        (A , B , C , tt*)
    ⊢ A ⊎B (B ⊎B C)
  fromTmA m (ρ , e , (x , y , z , tt*)) =
    (λ b → eval ρ (two (var zero) (var (suc zero) · var (suc (suc zero))) b))
    , e
    , (x
      , ((λ b → eval ρ (two (var (suc zero)) (var (suc (suc zero))) b))
        , Eq.refl
        , (y , z , tt*))
      , tt*)

⊎B-assoc : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → (A ⊎B B) ⊎B C ⊢ A ⊎B (B ⊎B C)
⊎B-assoc {ℓA = ℓA} {ℓB = ℓB} {ℓC = ℓC} {A = A} {B = B} {C = C} =
  fromTmA {A = A} {B = B} {C = C}
    ∘⊢ eqn→fun assoc (three ℓA ℓB ℓC) (A , B , C , tt*)
    ∘⊢ toTmA {A = A} {B = B} {C = C}

⊎Bmap : ∀ {ℓA ℓA' ℓB ℓB'} {A : TheoryTy ℓA tt} {A' : TheoryTy ℓA' tt}
        {B : TheoryTy ℓB tt} {B' : TheoryTy ℓB' tt}
  → A ⊢ A' → B ⊢ B' → A ⊎B B ⊢ A' ⊎B B'
⊎Bmap {ℓA} {ℓA'} {ℓB} {ℓB'} {A} {A'} {B} {B'} f g =
  ⊗map[ _⊙_ ][ two ℓA ℓB ] (two ℓA' ℓB')
    {As = A , B , tt*} {Bs = A' , B' , tt*}
    (λ where zero → f
             (suc zero) → g)

private
  toTmA⁻ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
    → A ⊎B (B ⊎B C)
    ⊢ ⟪ var zero · (var (suc zero) · var (suc (suc zero))) ⟫[ three ℓA ℓB ℓC ]
        (A , B , C , tt*)
  toTmA⁻ m (ms , e , (x , inner , tt*)) =
    ρ
    , Eq.pathToEq
        (cong (op _⊙_) (funExt (λ where
           zero → refl
           (suc zero) → cong (op _⊙_) (funExt (λ where
                          zero → refl
                          (suc zero) → refl))
                        ∙ Eq.eqToPath (inner .snd .fst)))
         ∙ Eq.eqToPath e)
    , (x , inner .snd .snd .fst , inner .snd .snd .snd .fst , tt*)
    where
    ρ : Fin 3 → Bag
    ρ = three (ms zero) (inner .fst zero) (inner .fst (suc zero))

  fromTmA⁻ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
    → ⟪ (var zero · var (suc zero)) · var (suc (suc zero)) ⟫[ three ℓA ℓB ℓC ]
        (A , B , C , tt*)
    ⊢ (A ⊎B B) ⊎B C
  fromTmA⁻ m (ρ , e , (x , y , z , tt*)) =
    (λ b → eval ρ (two (var zero · var (suc zero)) (var (suc (suc zero))) b))
    , e
    , ( ((λ b → eval ρ (two (var zero) (var (suc zero)) b))
        , Eq.refl
        , (x , y , tt*))
      , z , tt*)

⊎B-assoc⁻ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → A ⊎B (B ⊎B C) ⊢ (A ⊎B B) ⊎B C
⊎B-assoc⁻ {ℓA = ℓA} {ℓB = ℓB} {ℓC = ℓC} {A = A} {B = B} {C = C} =
  fromTmA⁻ {A = A} {B = B} {C = C}
    ∘⊢ eqn→inv assoc (three ℓA ℓB ℓC) (A , B , C , tt*)
    ∘⊢ toTmA⁻ {A = A} {B = B} {C = C}

⊗ᵘ→⊎B : (P : Fin 2 → TheoryTy ℓA tt)
  → ⊗ᵘ[ _⊙_ ] P ⊢ P zero ⊎B P (suc zero)
⊗ᵘ→⊎B P m (ms , e , h) = ms , e , (h zero , h (suc zero) , tt*)

⊎B→⊗ᵘ : (P : Fin 2 → TheoryTy ℓA tt)
  → P zero ⊎B P (suc zero) ⊢ ⊗ᵘ[ _⊙_ ] P
⊎B→⊗ᵘ P m (ms , e , (a , b , tt*)) = ms , e , two a b

bpair : Bag → Bag → Fin 2 → Bag
bpair = two

infixr 20 _⊙ᵖ_
_⊙ᵖ_ : Bag → Bag → Bag
a ⊙ᵖ b = op _⊙_ (bpair a b)

εᵖ : Bag
εᵖ = op ε· λ ()

opaque
  ⊙-comm : (a b : Bag) → a ⊙ᵖ b ≡ b ⊙ᵖ a
  ⊙-comm a b =
    M .snd .snd comm (bpair a b)
    ∙ cong (op _⊙_) (funExt λ where
        zero → refl
        (suc zero) → refl)

opaque
  ⊙-unitL : (a : Bag) → εᵖ ⊙ᵖ a ≡ a
  ⊙-unitL a =
    cong (op _⊙_) (funExt (λ where
      zero → cong (op ε·) (funExt λ ())
      (suc zero) → refl))
    ∙ M .snd .snd unitL (λ _ → a)

opaque
  ⊙-unitR : (a : Bag) → a ⊙ᵖ εᵖ ≡ a
  ⊙-unitR a =
    cong (op _⊙_) (funExt (λ where
      zero → refl
      (suc zero) → cong (op ε·) (funExt λ ())))
    ∙ M .snd .snd unitR (λ _ → a)

opaque
  ⊙-assoc : (a b c : Bag) → (a ⊙ᵖ b) ⊙ᵖ c ≡ a ⊙ᵖ (b ⊙ᵖ c)
  ⊙-assoc a b c =
    cong (op _⊙_) (funExt (λ where
      zero → cong (op _⊙_) (funExt λ where
               zero → refl
               (suc zero) → refl)
      (suc zero) → refl))
    ∙ M .snd .snd assoc (three a b c)
    ∙ cong (op _⊙_) (funExt (λ where
        zero → refl
        (suc zero) → cong (op _⊙_) (funExt λ where
                  zero → refl
                  (suc zero) → refl)))
    where
    triple' : Bag → Bag → Bag → Fin 3 → Bag
    triple' = three

opaque
  ⊙-inter : (a b c d : Bag) → (a ⊙ᵖ b) ⊙ᵖ (c ⊙ᵖ d) ≡ (a ⊙ᵖ c) ⊙ᵖ (b ⊙ᵖ d)
  ⊙-inter a b c d =
    ⊙-assoc a b (c ⊙ᵖ d)
    ∙ cong (a ⊙ᵖ_) (sym (⊙-assoc b c d) ∙ cong (_⊙ᵖ d) (⊙-comm b c)
                    ∙ ⊙-assoc c b d)
    ∙ sym (⊙-assoc a c (b ⊙ᵖ d))

εB→⌈ε⌉ : εB ⊢ ⌈ εᵖ ⌉
εB→⌈ε⌉ m (ms , e , tt*) = Eq.sym e Eq.∙ Eq.pathToEq (cong (op ε·) (funExt λ ()))

⌈ε⌉→εB : ⌈ εᵖ ⌉ ⊢ εB
⌈ε⌉→εB m Eq.refl = (λ ()) , Eq.refl , tt*

_⊸B_ : TheoryTy ℓA tt → TheoryTy ℓB tt → TheoryTy _ tt
(A ⊸B B) m = (ms : Fin 2 → Bag) → ms zero Eq.≡ m
           → (z : Bag) → op _⊙_ ms Eq.≡ z → A (ms (suc zero)) → B z

infixr 12 _⊸B_

⊸B-intro : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → A ⊎B B ⊢ C → A ⊢ B ⊸B C
⊸B-intro f m a ms Eq.refl z q b = f z (ms , q , (a , b , tt*))

⊸B-app : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → (A ⊸B B) ⊎B A ⊢ B
⊸B-app m (ms , e , (f , a , tt*)) = f ms Eq.refl m e a

⊸B-intro⁻ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → A ⊢ B ⊸B C → A ⊎B B ⊢ C
⊸B-intro⁻ {B = B} {C = C} f =
  ⊸B-app {A = B} {B = C} ∘⊢ ⊎Bmap f (id⊢ {A = B})

⊎B-unitL⁻ : {A : TheoryTy ℓA tt} → A ⊢ εB ⊎B A
⊎B-unitL⁻ m a =
  bpair εᵖ m , Eq.pathToEq (⊙-unitL m) , (((λ ()) , Eq.refl , tt*) , a , tt*)

⊎B-unitR⁻ : {A : TheoryTy ℓA tt} → A ⊢ A ⊎B εB
⊎B-unitR⁻ m a =
  bpair m εᵖ , Eq.pathToEq (⊙-unitR m) , (a , ((λ ()) , Eq.refl , tt*) , tt*)

K : ∀ {ℓ} → Type ℓ → TheoryTy ℓ tt
K P _ = P

K-elim : ∀ {ℓP} {P : Type ℓP} {A : TheoryTy ℓA tt} {C : TheoryTy ℓB tt}
  → (P → A ⊢ C) → K P & A ⊢ C
K-elim f m (p , a) = f p m a

K-out : ∀ {ℓP} {P : Type ℓP} {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → (K P & A) ⊎B B ⊢ K P & (A ⊎B B)
K-out m (ms , e , ((p , a) , b , tt*)) = p , (ms , e , (a , b , tt*))

⊎B⊕ᴰ-dist : ∀ {ℓY} {Y : Type ℓY} {A : Y → TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → (⊕[ y ∈ Y ] A y) ⊎B B ⊢ ⊕[ y ∈ Y ] (A y ⊎B B)
⊎B⊕ᴰ-dist m (ms , e , ((y , a) , b , tt*)) = y , (ms , e , (a , b , tt*))

Kmap : ∀ {ℓP ℓQ} {P : Type ℓP} {Q : Type ℓQ} → (P → Q) → K P ⊢ K Q
Kmap f _ = f

K-⊎B₁ : ∀ {ℓP} {P : Type ℓP} {B : TheoryTy ℓB tt} → K P ⊎B B ⊢ K P
K-⊎B₁ m (ms , e , (p , b , tt*)) = p

K-⊎B₂ : ∀ {ℓP} {P : Type ℓP} {A : TheoryTy ℓA tt} → A ⊎B K P ⊢ K P
K-⊎B₂ m (ms , e , (a , p , tt*)) = p

K-intro : ∀ {ℓP} {P : Type ℓP} {A : TheoryTy ℓA tt} → P → A ⊢ K P
K-intro p _ _ = p

private
  bη : (f : Fin 2 → Bag) → op _⊙_ f ≡ f zero ⊙ᵖ f (suc zero)
  bη f = cong (op _⊙_) (funExt (two refl refl))

⊎B-unitL : {A : TheoryTy ℓA tt} → εB ⊎B A ⊢ A
⊎B-unitL {A = A} m (ms , e , (z , a , tt*)) = subst A path a
  where
  path : ms (suc zero) ≡ m
  path =
    sym (⊙-unitL (ms (suc zero)))
    ∙ cong (_⊙ᵖ ms (suc zero)) (sym (Eq.eqToPath (εB→⌈ε⌉ (ms zero) z)))
    ∙ sym (bη ms)
    ∙ Eq.eqToPath e

⊎B-unitR : {A : TheoryTy ℓA tt} → A ⊎B εB ⊢ A
⊎B-unitR {A = A} m (ms , e , (a , z , tt*)) = subst A path a
  where
  path : ms zero ≡ m
  path =
    sym (⊙-unitR (ms zero))
    ∙ cong (ms zero ⊙ᵖ_) (sym (Eq.eqToPath (εB→⌈ε⌉ (ms (suc zero)) z)))
    ∙ sym (bη ms)
    ∙ Eq.eqToPath e

⊎B-unitL⌈⌉ : {a : Bag} → εB ⊎B ⌈ a ⌉ ⊢ ⌈ a ⌉
⊎B-unitL⌈⌉ m (ms , e , (z , w , tt*)) = Eq.pathToEq (sym path ∙ Eq.eqToPath w)
  where
  path : ms (suc zero) ≡ m
  path =
    sym (⊙-unitL (ms (suc zero)))
    ∙ cong (_⊙ᵖ ms (suc zero)) (sym (Eq.eqToPath (εB→⌈ε⌉ (ms zero) z)))
    ∙ sym (bη ms)
    ∙ Eq.eqToPath e
