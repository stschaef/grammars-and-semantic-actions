{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Precision of token grammars: a splitting whose left factor is a letter
   is pinned by the word, so refuting the right factor refutes the tensor. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Precise
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.List using ([] ; _∷_ ; _++_)
import Cubical.Data.List.Properties as L
open import Cubical.Data.Unit using (tt ; tt*)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Sat Alphabet isSetAlphabet using (satG)
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (castEq)
open import Theory.Instances.Monoid.Derivative Alphabet isSetAlphabet
  using (Dl ; Dl-string)
open import Theory.Type.Decidable.Base MonEqns Alphabet (λ _ → tt)
  listPresentation

private variable ℓA ℓB ℓC ℓD : Level

-- The head letter cannot be matched away (K forbids eliminating `c = c`),
-- so the split is flattened to a path and read off by cons-injectivity.
flat : (c : Alphabet) (u v w : ↓M tt)
  → u Eq.≡ (c ∷ []) → (u ++ v) Eq.≡ w → c ∷ v ≡ w
flat c u v w lc e = cong (_++ v) (sym (Eq.eqToPath lc)) ∙ Eq.eqToPath e

-- `flat` uses `∙`, so `subst` along it is a stuck `transp` even on
-- `Eq.refl`s; `Eq.transport A Eq.refl a = a` holds on the nose.
flatEq : (c : Alphabet) (u v w : ↓M tt)
  → u Eq.≡ (c ∷ []) → (u ++ v) Eq.≡ w → (c ∷ v) Eq.≡ w
flatEq c u v w Eq.refl Eq.refl = Eq.refl

Dl-ε : (c : Alphabet) → Dl c εTy ⊢ ⊥Ty
Dl-ε c m e = Empty.rec (L.¬nil≡cons (Eq.eqToPath (e .snd .fst)))

Dl-lit⊗ : (c d : Alphabet) {X : TheoryTy ℓA tt}
  → Dl c (literal d ⊗ X) ⊢ ⊕[ _ ∈ d ≡ c ] X
Dl-lit⊗ c d {X = X} m (ms , e , l , x , _) =
  L.cons-inj₁ headed , subst X (L.cons-inj₂ headed) x
  where
  headed : d ∷ ms (suc zero) ≡ c ∷ m
  headed = flat d (ms zero) (ms (suc zero)) (c ∷ m) l e

lit⊗-nil : {X : Type ℓA} (c : Alphabet) (u v : ↓M tt)
  → u Eq.≡ (c ∷ []) → (u ++ v) Eq.≡ [] → X
lit⊗-nil c u v lc e = Empty.rec (L.¬cons≡nil (flat c u v [] lc e))
tok⊗-precise : {A : TheoryTy ℓA tt} {K : TheoryTy ℓB tt}
  → A ⊢ char → A ⊗ ¬Ty K ⊢ ¬Ty (A ⊗ K)
tok⊗-precise {K = K} f m (ms , e , (a , (nk , _))) t =
  nk (subst K (sym (L.cons-inj₂ tails)) (t .snd .snd .snd .fst))
  where
  ns = t .fst
  here  = f (ms zero) a
  there = f (ns zero) (t .snd .snd .fst)
  tails : here .fst ∷ ms (suc zero) ≡ there .fst ∷ ns (suc zero)
  tails = flat (here .fst) (ms zero) (ms (suc zero)) m (here .snd) e
        ∙ sym (flat (there .fst) (ns zero) (ns (suc zero)) m
                 (there .snd) (t .snd .fst))

lit⊗-precise : {K : TheoryTy ℓA tt} (c : Alphabet)
  → literal c ⊗ ¬Ty K ⊢ ¬Ty (literal c ⊗ K)
lit⊗-precise c = tok⊗-precise λ _ lc → c , lc

char⊗-precise : {K : TheoryTy ℓA tt} → char ⊗ ¬Ty K ⊢ ¬Ty (char ⊗ K)
char⊗-precise = tok⊗-precise id⊢

sat⊗-precise : {P : Alphabet → Bool} {K : TheoryTy ℓA tt}
  → satG P ⊗ ¬Ty K ⊢ ¬Ty (satG P ⊗ K)
sat⊗-precise = tok⊗-precise λ _ (x , lc) → x .fst , lc

ε∉lit⊗ : {A : TheoryTy ℓA tt} (c : Alphabet) → εTy & (literal c ⊗ A) ⊢ ⊥Ty
ε∉lit⊗ c m ((ms , e , _) , (ns , f , (l , (a , _)))) =
  Empty.rec
    (L.¬cons≡nil
      (flat c (ns zero) (ns (suc zero)) m l f ∙ sym (Eq.eqToPath e)))

sameHead : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} (c d : Alphabet)
  → (literal c ⊗ A) & (literal d ⊗ B)
  ⊢ ⊕[ _ ∈ c ≡ d ] (literal c ⊗ (A & B))
sameHead {A = A} {B = B} c d m
  ((ms , e , (l , (a , _))) , (ns , f , (l' , (b , _)))) =
    L.cons-inj₁ heads , (ms , e , (l , ((a , subst B tails b) , tt*)))
  where
  heads : c ∷ ms (suc zero) ≡ d ∷ ns (suc zero)
  heads = flat c (ms zero) (ms (suc zero)) m l e
        ∙ sym (flat d (ns zero) (ns (suc zero)) m l' f)

  tails : ns (suc zero) ≡ ms (suc zero)
  tails = sym (L.cons-inj₂ heads)

dec-lit⊗↑ : {K : TheoryTy ℓA tt} (c : Alphabet)
  → literal c ⊗ DecTy K ⊢ DecTy (literal c ⊗ K)
dec-lit⊗↑ c = ⊕-elim dec-yes (dec-no ∘⊢ lit⊗-precise c) ∘⊢ ⊗⊕-distR

dec-char⊗↑ : {K : TheoryTy ℓA tt} → char ⊗ DecTy K ⊢ DecTy (char ⊗ K)
dec-char⊗↑ = ⊕-elim dec-yes (dec-no ∘⊢ char⊗-precise) ∘⊢ ⊗⊕-distR

levi : (u v u' v' : ↓M tt) → u ++ v ≡ u' ++ v'
  → (Σ[ d ∈ ↓M tt ] ((u' ≡ u ++ d) × (v ≡ d ++ v')))
    Sum.⊎ (Σ[ d ∈ ↓M tt ] ((u ≡ u' ++ d) × (v' ≡ d ++ v)))
levi [] v u' v' p = Sum.inl (u' , refl , p)
levi (c ∷ u) v [] v' p = Sum.inr (c ∷ u , refl , sym p)
levi (c ∷ u) v (d ∷ u') v' p with levi u v u' v' (L.cons-inj₂ p)
... | Sum.inl (e , q , r) = Sum.inl (e , cong₂ _∷_ (sym (L.cons-inj₁ p)) q , r)
... | Sum.inr (e , q , r) = Sum.inr (e , cong₂ _∷_ (L.cons-inj₁ p) q , r)

private
  -- `startsWith g`, spelled out so that this module need not name it
  headed : (g : Alphabet) (d v : ↓M tt) → v ≡ g ∷ d → (literal g ⊗ ⊤Ty) v
  headed g d v r = two (g ∷ []) d , Eq.pathToEq (sym r) , (Eq.refl , (tt , tt*))

  ⊗headed : {X : TheoryTy ℓA tt} (g : Alphabet) (x d u : ↓M tt)
    → X x → u ≡ x ++ (g ∷ d) → (X ⊗ (literal g ⊗ ⊤Ty)) u
  ⊗headed g x d u a q =
    two x (g ∷ d) , Eq.pathToEq (sym q) , (a , (headed g d (g ∷ d) refl , tt*))

-- If Levi's `d` is a letter `g`, a separation hypothesis at `g` refutes
-- it; with the proper cases refuted the two splittings coincide.
module _ {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
         {C : TheoryTy ℓC tt} {D : TheoryTy ℓD tt}
  (sepL : (g : Alphabet)
    → ((A ⊗ (literal g ⊗ ⊤Ty)) & C ⊢ ⊥Ty)
      Sum.⊎ (((literal g ⊗ ⊤Ty) & B) ⊢ ⊥Ty))
  (sepR : (g : Alphabet)
    → ((C ⊗ (literal g ⊗ ⊤Ty)) & A ⊢ ⊥Ty)
      Sum.⊎ (((literal g ⊗ ⊤Ty) & D) ⊢ ⊥Ty))
  where
  private
    agree : (x y x' y' : ↓M tt) → A x → B y → C x' → D y'
      → (Σ[ d ∈ ↓M tt ] ((x' ≡ x ++ d) × (y ≡ d ++ y')))
        Sum.⊎ (Σ[ d ∈ ↓M tt ] ((x ≡ x' ++ d) × (y' ≡ d ++ y)))
      → (x ≡ x') × (y ≡ y')
    agree x y x' y' a b c d (Sum.inl ([] , q , r)) =
      sym (q ∙ L.++-unit-r x) , r
    agree x y x' y' a b c d (Sum.inl (g ∷ ds , q , r)) =
      Sum.rec (λ h → Empty.rec (h x' (⊗headed g x ds x' a q , c) .lower))
              (λ h → Empty.rec (h y (headed g (ds ++ y') y r , b) .lower))
              (sepL g)
    agree x y x' y' a b c d (Sum.inr ([] , q , r)) =
      q ∙ L.++-unit-r x' , sym r
    agree x y x' y' a b c d (Sum.inr (g ∷ ds , q , r)) =
      Sum.rec (λ h → Empty.rec (h x (⊗headed g x' ds x c q , a) .lower))
              (λ h → Empty.rec (h y' (headed g (ds ++ y) y' r , d) .lower))
              (sepR g)

  splitAgree : (x y x' y' : ↓M tt) → (x ++ y) ≡ (x' ++ y')
    → A x → B y → C x' → D y' → (x ≡ x') × (y ≡ y')
  splitAgree x y x' y' p a b c d =
    agree x y x' y' a b c d (levi x y x' y' p)

  ⊗&-align : (A ⊗ B) & (C ⊗ D) ⊢ (A & C) ⊗ (B & D)
  ⊗&-align m ((ms , e , (a , (b , _))) , (ns , e' , (c , (d , _)))) =
    two (ms zero) (ms (suc zero)) , e
    , ((a , subst C (sym (pf .fst)) c) , ((b , subst D (sym (pf .snd)) d) , tt*))
    where
    pf = splitAgree (ms zero) (ms (suc zero)) (ns zero) (ns (suc zero))
           (Eq.eqToPath e ∙ sym (Eq.eqToPath e')) a b c d
module _ {ℓA : Level} {A : TheoryTy ℓA tt} where

  Dl-absorb : (c : Alphabet) (w : ↓M tt)
    → literal c ⊗ Dl-string (w ++ (c ∷ [])) A ⊢ Dl-string w A
  Dl-absorb c w m (ms , e , (lc , (a , _))) =
    castEq {A = λ z → A (w ++ z)} e
      (castEq {A = λ z → A (w ++ (z ++ ms (suc zero)))} (Eq.sym lc)
        (castEq {A = A} (++-assocEq w (c ∷ []) (ms (suc zero))) a))

  Dl-absorb⁻ : (c : Alphabet) (w : ↓M tt)
    → (literal c ⊗ ⊤Ty) & Dl-string w A
    ⊢ literal c ⊗ Dl-string (w ++ (c ∷ [])) A
  Dl-absorb⁻ c w m ((ms , e , (lc , _)) , a) =
    ms , e ,
      (lc , (castEq {A = A} (Eq.sym (++-assocEq w (c ∷ []) (ms (suc zero))))
              (castEq {A = λ z → A (w ++ (z ++ ms (suc zero)))} lc
                (castEq {A = λ z → A (w ++ z)} (Eq.sym e) a))
            , tt*))
