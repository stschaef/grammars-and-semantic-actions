{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The two residuals of the free monoid's multiplication, together with the
   structural maps of the convolution that a shift-reduce parser composes.

   Every definition here introduces a *connective* by matching on its own
   elements: this is the tier of `⊗-assoc` in `Strings.agda` and of
   `⊗ᵘ-elim` in `Theory.Type.Operation.Base`, not of reasoning inside the
   DSL.  Nothing downstream of this file binds a model element. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.Residual
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List as L using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Sigma using (_,_ ; Σ-syntax)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)
import Cubical.Data.Sum as Sum
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
import Theory.Type.Residual.Base MonEqns Alphabet (λ _ → tt) listPresentation
  as R


private variable ℓ ℓ' ℓ'' ℓY : Level

-- `Eq.transport` goes through `subst`, so it leaves an `hcomp` even at
-- `Eq.refl`; matching the equation instead is what makes every cast below
-- vanish on canonical input.
castEq : {A : ↓M tt → Type ℓ} {x y : ↓M tt} → x Eq.≡ y → A x → A y
castEq Eq.refl a = a

-- `castEq` at a proof whose ends are definitionally equal, as a `PathP`:
-- the index is a set, so which path it is taken along never matters.
castEqPathP : {A : ↓M tt → Type ℓ} {x y : ↓M tt} (q : x Eq.≡ y) (p : y ≡ x)
  (a : A x) → PathP (λ j → A (p j)) (castEq {A = A} q a) a
castEqPathP {A = A} Eq.refl p a =
  subst (λ r → PathP (λ j → A (r j)) a a) (isSetString _ _ refl p) refl

-- The unit and associativity laws are stated in `Eq`, by matching the
-- index equations rather than composing paths -- `++-assocEq` and
-- `++-unit-rEq` come from `Strings`, where `⊗-assoc` needs them for the
-- same reason.


-- `Fin 2` has no definitional η, so a reassembled splitting needs this path.
two-η : {P : Fin 2 → Type ℓ} (f : (i : Fin 2) → P i)
  → two (f zero) (f (suc zero)) ≡ f
two-η f = funExt λ where
  zero → refl
  (suc zero) → refl

⊗-split-η : {A : TheoryTy ℓ tt} {B : TheoryTy ℓ' tt}
  (ms : Fin 2 → ↓M tt) (a : A (ms zero)) (b : B (ms (suc zero)))
  → Path ((A ⊗ B) (ms zero ++ ms (suc zero)))
      (two (ms zero) (ms (suc zero)) , Eq.refl , (a , (b , tt*)))
      (ms , Eq.refl , (a , (b , tt*)))
⊗-split-η ms a b i = two-η ms i , Eq.refl , (a , (b , tt*))

-- The right residual.  This is `Resid` at `_⊙_`'s slot `zero`, written out
-- so that the unused focused-slot level does not show up in a `Lift`.

_⟜_ : TheoryTy ℓ tt → TheoryTy ℓ' tt → TheoryTy _ tt
(C ⟜ B) m = (r : ↓M tt) → B r → C (m ++ r)

infixl 12 _⟜_

⟜→Resid : {B : TheoryTy ℓ tt} {C : TheoryTy ℓ' tt}
  → C ⟜ B ⊢ R.Resid _⊙_ (two ℓ-zero ℓ) (⊤Ty , B , tt*) zero C
⟜→Resid m f hs (lift (b , _)) = f (hs zero) b

Resid→⟜ : {B : TheoryTy ℓ tt} {C : TheoryTy ℓ' tt}
  → R.Resid _⊙_ (two ℓ-zero ℓ) (⊤Ty , B , tt*) zero C ⊢ C ⟜ B
Resid→⟜ m f r b = f (λ _ → r) (lift (b , tt*))

module _ {A : TheoryTy ℓ tt} {B : TheoryTy ℓ' tt} {C : TheoryTy ℓ'' tt} where
  ⟜-intro : A ⊗ B ⊢ C → A ⊢ C ⟜ B
  ⟜-intro e m a r b = e (m ++ r) (two m r , Eq.refl , (a , (b , tt*)))

  ⟜-intro⁻ : A ⊢ C ⟜ B → A ⊗ B ⊢ C
  ⟜-intro⁻ f m (ms , e , (a , (b , _))) =
    castEq {A = C} e (f (ms zero) a (ms (suc zero)) b)

  -- β spends the split's equation and then `⊗-split-η`; η is on the nose.
  ⟜-β : (e : A ⊗ B ⊢ C) → ⟜-intro⁻ (⟜-intro e) ≡ e
  ⟜-β e = funExt λ m → funExt λ where
    (ms , Eq.refl , (a , (b , _))) → cong (e _) (⊗-split-η ms a b)

  ⟜-η : (f : A ⊢ C ⟜ B) → ⟜-intro (⟜-intro⁻ f) ≡ f
  ⟜-η f = refl

  ⟜Iso : Iso (A ⊗ B ⊢ C) (A ⊢ C ⟜ B)
  ⟜Iso .Iso.fun = ⟜-intro
  ⟜Iso .Iso.inv = ⟜-intro⁻
  ⟜Iso .Iso.sec = ⟜-η
  ⟜Iso .Iso.ret = ⟜-β

⟜-app : {B : TheoryTy ℓ tt} {C : TheoryTy ℓ' tt} → (C ⟜ B) ⊗ B ⊢ C
⟜-app = ⟜-intro⁻ id⊢

⟜-precomp : {B : TheoryTy ℓ tt} {B' : TheoryTy ℓ' tt} {C : TheoryTy ℓ'' tt}
  → B' ⊢ B → C ⟜ B ⊢ C ⟜ B'
⟜-precomp g m f r b = f r (g r b)

⟜-post : {B : TheoryTy ℓ tt} {C : TheoryTy ℓ' tt} {C' : TheoryTy ℓ'' tt}
  → C ⊢ C' → C ⟜ B ⊢ C' ⟜ B
⟜-post h m f r b = h (m ++ r) (f r b)

-- uncurrying one factor off the right, the only place associativity is spent
⟜-uncurry : {A : TheoryTy ℓ tt} {B : TheoryTy ℓ' tt} {C : TheoryTy ℓ'' tt}
  → (C ⟜ (A ⊗ B)) ⊗ A ⊢ C ⟜ B
⟜-uncurry {A = A} {B = B} {C = C} m (ms , e , (f , (a , _))) r b =
  reassocSplit (ms zero) (ms (suc zero)) m f a e
  where
  reassocSplit : (x y w : ↓M tt) → (C ⟜ (A ⊗ B)) x → A y
    → (x ++ y) Eq.≡ w → C (w ++ r)
  reassocSplit x y w f' a' Eq.refl =
    castEq {A = C} (Eq.sym (++-assocEq x y r))
      (f' (y ++ r) (two y r , Eq.refl , (a' , (b , tt*))))

⟜-unitr : {C : TheoryTy ℓ tt} → C ⟜ εTy ⊢ C
⟜-unitr {C = C} m f = castEq {A = C} (++-unit-rEq m) (f [] εTy-pt)

-- The left residual: a map out of the remaining input still awaiting
-- something on its left.

_⊸_ : TheoryTy ℓ tt → TheoryTy ℓ' tt → TheoryTy _ tt
(A ⊸ C) m = (l : ↓M tt) → A l → C (l ++ m)

infixr 12 _⊸_

-- The transpose of `(A ⊗ -) ⊣ (A ⊸ -)`: `A` is the *left* factor, so it is
-- the right-hand factor of the tensor that moves.
module _ {A : TheoryTy ℓ tt} {B : TheoryTy ℓ' tt} {C : TheoryTy ℓ'' tt} where
  ⊸-lam : A ⊗ B ⊢ C → B ⊢ A ⊸ C
  ⊸-lam e m b l a = e (l ++ m) (two l m , Eq.refl , (a , (b , tt*)))

  ⊸-lam⁻ : B ⊢ A ⊸ C → A ⊗ B ⊢ C
  ⊸-lam⁻ f m (ms , e , (a , (b , _))) =
    castEq {A = C} e (f (ms (suc zero)) b (ms zero) a)

  ⊸-lam-β : (e : A ⊗ B ⊢ C) → ⊸-lam⁻ (⊸-lam e) ≡ e
  ⊸-lam-β e = funExt λ m → funExt λ where
    (ms , Eq.refl , (a , (b , _))) → cong (e _) (⊗-split-η ms a b)

  ⊸-lam-η : (f : B ⊢ A ⊸ C) → ⊸-lam (⊸-lam⁻ f) ≡ f
  ⊸-lam-η f = refl

  ⊸-lamIso : Iso (A ⊗ B ⊢ C) (B ⊢ A ⊸ C)
  ⊸-lamIso .Iso.fun = ⊸-lam
  ⊸-lamIso .Iso.inv = ⊸-lam⁻
  ⊸-lamIso .Iso.sec = ⊸-lam-η
  ⊸-lamIso .Iso.ret = ⊸-lam-β

⊸-app : {A : TheoryTy ℓ tt} {C : TheoryTy ℓ' tt} → A ⊗ (A ⊸ C) ⊢ C
⊸-app {C = C} m (ms , e , (a , (f , _))) = castEq {A = C} e (f (ms zero) a)

⊸-precomp : {A : TheoryTy ℓ tt} {A' : TheoryTy ℓ' tt} {C : TheoryTy ℓ'' tt}
  → A' ⊢ A → A ⊸ C ⊢ A' ⊸ C
⊸-precomp g m f l a = f l (g l a)

⊸-post : {A : TheoryTy ℓ tt} {C : TheoryTy ℓ' tt} {C' : TheoryTy ℓ'' tt}
  → C ⊢ C' → A ⊸ C ⊢ A ⊸ C'
⊸-post h m f l a = h (l ++ m) (f l a)

-- Currying *reverses*: the outer residual is awaited furthest to the left,
-- so `A` -- the earlier word of the pair -- ends up innermost.
⊸-curry : {A : TheoryTy ℓ tt} {B : TheoryTy ℓ' tt} {C : TheoryTy ℓ'' tt}
  → (A ⊗ B) ⊸ C ⊢ B ⊸ (A ⊸ C)
⊸-curry {C = C} m f l' b l a =
  castEq {A = C} (++-assocEq l l' m)
    (f (l ++ l') (two l l' , Eq.refl , (a , (b , tt*))))

⊸-uncurry : {A : TheoryTy ℓ tt} {B : TheoryTy ℓ' tt} {C : TheoryTy ℓ'' tt}
  → B ⊸ (A ⊸ C) ⊢ (A ⊗ B) ⊸ C
⊸-uncurry {A = A} {B = B} {C = C} m f l (ms , e , (a , (b , _))) =
  applyAtSplit (ms zero) (ms (suc zero)) l a b e
  where
  applyAtSplit : (x y w : ↓M tt) → A x → B y → (x ++ y) Eq.≡ w → C (w ++ m)
  applyAtSplit x y w a' b' Eq.refl =
    castEq {A = C} (Eq.sym (++-assocEq x y m)) (f y b' x a')

-- Feeding the left slot at the unit: how a parser is started.
⊸-unitl : {A : TheoryTy ℓ tt} {C : TheoryTy ℓ' tt} → εTy ⊢ A → A ⊸ C ⊢ C
⊸-unitl p m f = f [] (p [] εTy-pt)

-- Moving a consumed factor from the input side to the awaited side: a `shift`.
⊸⟜-swap : {A : TheoryTy ℓ tt} {B : TheoryTy ℓ' tt} {C : TheoryTy ℓ'' tt}
  → A ⊗ (B ⊸ C) ⊢ (B ⟜ A) ⊸ C
⊸⟜-swap {A = A} {B = B} {C = C} m (ms , e , (a , (f , _))) l g =
  shiftAtSplit (ms zero) (ms (suc zero)) m a f e
  where
  shiftAtSplit : (x y w : ↓M tt) → A x → (B ⊸ C) y
    → (x ++ y) Eq.≡ w → C (l ++ w)
  shiftAtSplit x y w a' f' Eq.refl =
    castEq {A = C} (++-assocEq l x y) (f' (l ++ x) (g x a'))

⊸⊕ᴰ : {Y : Type ℓY} {A : Y → TheoryTy ℓ tt} {C : TheoryTy ℓ' tt}
  → &[ y ∈ Y ] (A y ⊸ C) ⊢ (⊕[ y ∈ Y ] A y) ⊸ C
⊸⊕ᴰ m f l (y , a) = f y l a

-- Convolution plumbing.  `Fin 2` has no definitional η, so the passage
-- between an operation's convolution and the binary tensor is stated once.

⊗ᵘ→⊗ : (P : Fin 2 → TheoryTy ℓ tt) → ⊗ᵘ[ _⊙_ ] P ⊢ P zero ⊗ P (suc zero)
⊗ᵘ→⊗ P m (ms , e , xs) = ms , e , (xs zero , (xs (suc zero) , tt*))

⊗→⊗ᵘ : (P : Fin 2 → TheoryTy ℓ tt) → P zero ⊗ P (suc zero) ⊢ ⊗ᵘ[ _⊙_ ] P
⊗→⊗ᵘ P m (ms , e , (a , (b , _))) = ms , e , λ where
  zero → a
  (suc zero) → b

-- The same passage at a code, the form every client of `μ` meets it in.
-- Writing the slot family out is all `two`'s missing η needs.
module _ {ℓA ℓB ℓX} {X : Type ℓX} {xs : X → Unit}
  {A : (x : X) → TheoryTy ℓB tt} (Fa Fb : Functor ℓA X xs tt) where

  ⟦⊗e⟧ : ⟦ ⊗e _⊙_ (two Fa Fb) ⟧TheoryTy A
       ⊢ ⟦ Fa ⟧TheoryTy A ⊗ ⟦ Fb ⟧TheoryTy A
  ⟦⊗e⟧ = ⊗ᵘ→⊗ (λ i → ⟦ two Fa Fb i ⟧TheoryTy A)

  ⟦⊗e⟧⁻ : ⟦ Fa ⟧TheoryTy A ⊗ ⟦ Fb ⟧TheoryTy A
        ⊢ ⟦ ⊗e _⊙_ (two Fa Fb) ⟧TheoryTy A
  ⟦⊗e⟧⁻ = ⊗→⊗ᵘ (λ i → ⟦ two Fa Fb i ⟧TheoryTy A)

⊗ε-unit-l⁻ : {A : TheoryTy ℓ tt} → A ⊢ εTy ⊗ A
⊗ε-unit-l⁻ m a = two [] m , Eq.refl , (εTy-pt , (a , tt*))

⊗ε-unit-r⁻ : {A : TheoryTy ℓ tt} → A ⊢ A ⊗ εTy
⊗ε-unit-r⁻ m a =
  two m [] , ++-unit-rEq m , (a , (εTy-pt , tt*))

⊗ε-unit-r : {A : TheoryTy ℓ tt} → A ⊗ εTy ⊢ A
⊗ε-unit-r {A = A} m (ms , e , (a , (u , _))) =
  atEmptyRight (ms zero) (ms (suc zero)) m a (u .snd .fst) e
  where
  atEmptyRight : (x y w : ↓M tt) → A x → [] Eq.≡ y → (x ++ y) Eq.≡ w → A w
  atEmptyRight x .[] w a' Eq.refl r =
    castEq {A = A} r (castEq {A = A} (Eq.sym (++-unit-rEq x)) a')

⊗-unit-l⁻-nat : {K : TheoryTy ℓ tt} {L : TheoryTy ℓ' tt} (f : K ⊢ L)
  → ⊗ε-unit-l⁻ ∘⊢ f ≡ ⊗-map (id⊢ {A = εTy}) f ∘⊢ ⊗ε-unit-l⁻
⊗-unit-l⁻-nat f = refl

-- The transform's four triangles.  They mention `εTy`'s unitors, so they
-- live here rather than beside `⊗-pent` in `Strings`.
module _ {A : TheoryTy ℓ tt} {K : TheoryTy ℓ' tt} where

  private
    triL : A ⊗ K ⊢ A ⊗ K
    triL = ⊗-map (⊗-unit-l {A = A}) (id⊢ {A = K})
      ∘⊢ ⊗-assoc⁻ {A = εTy} {B = A} {C = K}
      ∘⊢ ⊗ε-unit-l⁻ {A = A ⊗ K}

    -- named so `⊗-tri-l⁻` can hand `unit-l≡` the tuple it transports
    triL⁻in : A ⊗ K ⊢ εTy ⊗ (A ⊗ K)
    triL⁻in = ⊗-assoc {A = εTy} {B = A} {C = K}
      ∘⊢ ⊗-map (⊗ε-unit-l⁻ {A = A}) (id⊢ {A = K})

    triL⁻ : A ⊗ K ⊢ A ⊗ K
    triL⁻ = ⊗-unit-l {A = A ⊗ K} ∘⊢ triL⁻in

    triR : A ⊗ K ⊢ A ⊗ K
    triR = ⊗-map (⊗ε-unit-r {A = A}) (id⊢ {A = K})
      ∘⊢ ⊗-assoc⁻ {A = A} {B = εTy} {C = K}
      ∘⊢ ⊗-map (id⊢ {A = A}) (⊗ε-unit-l⁻ {A = K})

    triR⁻ : A ⊗ K ⊢ A ⊗ K
    triR⁻ = ⊗-map (id⊢ {A = A}) (⊗-unit-l {A = K})
      ∘⊢ ⊗-assoc {A = A} {B = εTy} {C = K}
      ∘⊢ ⊗-map (⊗ε-unit-r⁻ {A = A}) (id⊢ {A = K})

  -- the empty half of the split is dropped by `⊗-unit-l`, at `refl`
  ⊗-tri-l : triL ≡ id⊢
  ⊗-tri-l = funExt λ m → funExt (atPoint m)
    where
    atPoint : (m : ↓M tt) (x : (A ⊗ K) m) → triL m x ≡ x
    atPoint m (ms , e , (a , (k' , _))) =
      ⊗PathP' {A = A} {B = K} refl (two≡ refl refl)
        (symP (unit-l≡ {A = A} (ms zero)
                (two [] (ms zero) , Eq.refl , (εTy-pt , (a , tt*))) refl))
        refl

  -- the other way round the transport lands on the whole pair, so the
  -- split's own equation is the path it is taken along
  ⊗-tri-l⁻ : triL⁻ ≡ id⊢
  ⊗-tri-l⁻ = funExt λ m → funExt (atPoint m)
    where
    atPoint : (m : ↓M tt) (x : (A ⊗ K) m) → triL⁻ m x ≡ x
    atPoint m x@(ms , e , (a , (k' , _))) =
      sym (fromPathP (unit-l≡ {A = A ⊗ K} m (triL⁻in m x) (Eq.eqToPath e)))
      ∙ fromPathP (⊗PathP' {A = A} {B = K}
          (Eq.eqToPath e) (two≡ refl refl) refl refl)

  -- an empty *right* half instead: `⊗ε-unit-r` pays `++-unit-r`
  ⊗-tri-r : triR ≡ id⊢
  ⊗-tri-r = funExt λ m → funExt (atPoint m)
    where
    atPoint : (m : ↓M tt) (x : (A ⊗ K) m) → triR m x ≡ x
    atPoint m (ms , e , (a , (k' , _))) =
      ⊗PathP' {A = A} {B = K} refl (two≡ (L.++-unit-r (ms zero)) refl)
        (castEqPathP {A = A} (Eq.sym (++-unit-rEq (ms zero)))
          (L.++-unit-r (ms zero)) a)
        refl

  ⊗-tri-r⁻ : triR⁻ ≡ id⊢
  ⊗-tri-r⁻ = funExt λ m → funExt (atPoint m)
    where
    atPoint : (m : ↓M tt) (x : (A ⊗ K) m) → triR⁻ m x ≡ x
    atPoint m (ms , e , (a , (k' , _))) =
      ⊗PathP' {A = A} {B = K} refl (two≡ refl refl) refl
        (symP (unit-l≡ {A = K} (ms (suc zero))
                (two [] (ms (suc zero)) , Eq.refl , (εTy-pt , (k' , tt*)))
                refl))

-- concatenation of representables, in both directions: the free monoid's
-- multiplication *is* the tensor of the words it multiplies
⌈⌉-cat : (u v : ↓M tt) → ⌈ u ⌉ ⊗ ⌈ v ⌉ ⊢ ⌈ u ++ v ⌉
⌈⌉-cat u v m (ms , e , (p , (q , _))) =
  atSplit (ms zero) (ms (suc zero)) m p q e
  where
  atSplit : (x y w : ↓M tt) → x Eq.≡ u → y Eq.≡ v
    → (x ++ y) Eq.≡ w → w Eq.≡ (u ++ v)
  atSplit .u .v w Eq.refl Eq.refl r = Eq.sym r

⌈⌉-split : (u v : ↓M tt) → ⌈ u ++ v ⌉ ⊢ ⌈ u ⌉ ⊗ ⌈ v ⌉
⌈⌉-split u v m p = atConcatEq p
  where
  atConcatEq : m Eq.≡ (u ++ v) → (⌈ u ⌉ ⊗ ⌈ v ⌉) m
  atConcatEq Eq.refl = two u v , Eq.refl , (Eq.refl , (Eq.refl , tt*))

-- the unit law, at a representable: Eq-clean, unlike `⊗-unit-l`
ε⌈⌉-unit-l : (v : ↓M tt) → εTy ⊗ ⌈ v ⌉ ⊢ ⌈ v ⌉
ε⌈⌉-unit-l v m (ms , e , (u , (q , _))) =
  atEmptyLeft (ms zero) (ms (suc zero)) m (u .snd .fst) q e
  where
  atEmptyLeft : (x y w : ↓M tt) → [] Eq.≡ x → y Eq.≡ v
    → (x ++ y) Eq.≡ w → w Eq.≡ v
  atEmptyLeft .[] .v w Eq.refl Eq.refl r = Eq.sym r

⊗⊕ᴰ-distL : {Y : Type ℓY} {A : Y → TheoryTy ℓ tt} {C : TheoryTy ℓ' tt}
  → (⊕[ y ∈ Y ] A y) ⊗ C ⊢ ⊕[ y ∈ Y ] (A y ⊗ C)
⊗⊕ᴰ-distL m (ms , e , ((y , a) , (c , _))) = y , (ms , e , (a , (c , tt*)))

⊗⊕ᴰ-distR : {Y : Type ℓY} {A : TheoryTy ℓ tt} {C : Y → TheoryTy ℓ' tt}
  → A ⊗ (⊕[ y ∈ Y ] C y) ⊢ ⊕[ y ∈ Y ] (A ⊗ C y)
⊗⊕ᴰ-distR m (ms , e , (a , ((y , c) , _))) = y , (ms , e , (a , (c , tt*)))

&⊕-distR : {A : TheoryTy ℓ tt} {B : TheoryTy ℓ' tt} {C : TheoryTy ℓ'' tt}
  → A & (B ⊕ C) ⊢ (A & B) ⊕ (A & C)
&⊕-distR m (a , Sum.inl b) = Sum.inl (a , b)
&⊕-distR m (a , Sum.inr c) = Sum.inr (a , c)

&⊕ᴰ-distR : {A : TheoryTy ℓ tt} {Y : Type ℓY} {B : Y → TheoryTy ℓ' tt}
  → A & (⊕[ y ∈ Y ] B y) ⊢ ⊕[ y ∈ Y ] (A & B y)
&⊕ᴰ-distR m (a , (y , b)) = y , (a , b)

&⊕ᴰ-distL : {Y : Type ℓY} {A : Y → TheoryTy ℓ tt} {B : TheoryTy ℓ' tt}
  → (⊕[ y ∈ Y ] A y) & B ⊢ ⊕[ y ∈ Y ] (A y & B)
&⊕ᴰ-distL m ((y , a) , b) = y , (a , b)

-- The constant type, carrying a metalanguage type through the DSL, with its
-- functorial action and its points.  A `⊕ᴰ` tag can then be constrained by an
-- equation, which is what pins a stack to one symbol string.
Konst : {s : Sorts} → Type ℓ → TheoryTy ℓ s
Konst X _ = X

Konst-map : {X : Type ℓ} {Y : Type ℓ'} → (X → Y) → Konst {s = tt} X ⊢ Konst Y
Konst-map g _ = g

Konst-pt : {X : Type ℓ} {A : TheoryTy ℓ' tt} → X → A ⊢ Konst X
Konst-pt x _ _ = x
