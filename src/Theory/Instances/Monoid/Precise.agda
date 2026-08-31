{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Precision of the token grammars: a splitting whose left factor is a
   letter is determined by the whole word, so a refutation of the right
   factor refutes the tensor.  This is what turns a decision under a token
   into a decision of the tensor, and it is a fact about `literal`/`char`,
   not about any parser. -}
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

-- The head letter cannot be matched away -- `(c ∷ []) ++ v ≟ c ∷ as` would
-- eliminate the reflexive equation `c = c`, which K forbids -- so the split
-- is flattened to a path and read off by cons-injectivity.
flat : (c : Alphabet) (u v w : ↓M tt)
  → u Eq.≡ (c ∷ []) → (u ++ v) Eq.≡ w → c ∷ v ≡ w
flat c u v w lc e = cong (_++ v) (sym (Eq.eqToPath lc)) ∙ Eq.eqToPath e

-- The same fact in the Eq world.  `flat` composes its two inputs with `∙`,
-- so a `subst` along it is a stuck `transp` even when both are `Eq.refl`;
-- `Eq.transport A Eq.refl a = a` holds on the nose, which is what lets a
-- witness transported through it be projected back out.
flatEq : (c : Alphabet) (u v w : ↓M tt)
  → u Eq.≡ (c ∷ []) → (u ++ v) Eq.≡ w → (c ∷ v) Eq.≡ w
flatEq c u v w Eq.refl Eq.refl = Eq.refl

-- Under a derivative, `ε` is refuted and a leading literal is pinned:
-- these are the two ways a one-step unrolling meets `Dl`, and both are
-- the precision of `literal` again.
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

lit⊗-head : {X : Type ℓA} (c a : Alphabet) (u v as : ↓M tt)
  → (a Eq.≡ c → Empty.⊥)
  → u Eq.≡ (c ∷ []) → (u ++ v) Eq.≡ (a ∷ as) → X
lit⊗-head c a u v as ne lc e =
  Empty.rec (ne (Eq.pathToEq (sym (L.cons-inj₁ (flat c u v (a ∷ as) lc e)))))

lit⊗-tail : {B : TheoryTy ℓA tt} (c : Alphabet) (u v as : ↓M tt)
  → u Eq.≡ (c ∷ []) → (u ++ v) Eq.≡ (c ∷ as) → B v → B as
lit⊗-tail {B = B} c u v as lc e =
  subst B (L.cons-inj₂ (flat c u v (c ∷ as) lc e))

-- A grammar every one of whose parses is a single character is *precise*:
-- the splitting of `A ⊗ K` is determined by the word, so a refutation of
-- the suffix refutes the whole tensor.  `literal c`, `char` and `satG P`
-- are all of that shape, and the three lemmas below are this one lemma at
-- the three maps into `char`; only the map differs, never the argument.
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

-- `literal c` is precise: two splittings with the same one-letter prefix
-- agree on the suffix, so refuting the suffix refutes the whole tensor.
lit⊗-precise : {K : TheoryTy ℓA tt} (c : Alphabet)
  → literal c ⊗ ¬Ty K ⊢ ¬Ty (literal c ⊗ K)
lit⊗-precise c = tok⊗-precise λ _ lc → c , lc

-- ...and so is `char`, which fixes the splitting without fixing the letter
char⊗-precise : {K : TheoryTy ℓA tt} → char ⊗ ¬Ty K ⊢ ¬Ty (char ⊗ K)
char⊗-precise = tok⊗-precise id⊢

-- ...and so is `satG P`, whose parse carries the letter and a proof that
-- the predicate accepts it.  Stated here rather than in `Regex/Sat`,
-- beside the other two, so that the argument is written once.
sat⊗-precise : {P : Alphabet → Bool} {K : TheoryTy ℓA tt}
  → satG P ⊗ ¬Ty K ⊢ ¬Ty (satG P ⊗ K)
sat⊗-precise = tok⊗-precise λ _ (x , lc) → x .fst , lc

-- Two more consequences of the same precision, both used wherever two
-- one-step unrollings are compared: a `literal`-headed word is not empty,
-- and two such words agree on their head letter.
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

-- The one-token derivative as a term rather than a case split: a decision
-- under the letter is a decision of the tensor.
dec-lit⊗↑ : {K : TheoryTy ℓA tt} (c : Alphabet)
  → literal c ⊗ DecTy K ⊢ DecTy (literal c ⊗ K)
dec-lit⊗↑ c = ⊕-elim dec-yes (dec-no ∘⊢ lit⊗-precise c) ∘⊢ ⊗⊕-distR

dec-char⊗↑ : {K : TheoryTy ℓA tt} → char ⊗ DecTy K ⊢ DecTy (char ⊗ K)
dec-char⊗↑ = ⊕-elim dec-yes (dec-no ∘⊢ char⊗-precise) ∘⊢ ⊗⊕-distR

-- Levi's lemma, and the alignment of two splittings that it powers.

-- Two factorisations of one word are nested: one left factor is the other
-- extended by some `d`.
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

-- Levi says the two left factors differ by a `d`; if `d` is a letter `g`
-- then `g` both continues one left factor into the other and opens the
-- other's right factor, so a separation hypothesis at `g` refutes it.
-- With every proper case refuted the two splittings coincide and the
-- factors pair up.  This is the internal replacement for the old
-- `SplittingTrichotomy`-based `⊗&-distL≅`.
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

  -- The two cuts coincide.  This is the whole content; `⊗&-align` below
  -- repackages it as a term, and `unambiguous⊗` needs it as a path.
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

-- The derivative of a matching literal is `ε`, and a literal can be absorbed
-- into the prefix a `Dl-string` is taken at, in both directions.  These are
-- the terms an LR machine's shift is, and they live here for the same reason
-- `Dl-lit⊗` does: they match on a splitting, which nothing above this tier
-- may do.

Dl-lit-ε : (c : Alphabet) → εTy ⊢ Dl c (literal c)
Dl-lit-ε c m (ms , e , _) = go m e
  where
  go : (u : ↓M tt) → [] Eq.≡ u → (c ∷ u) Eq.≡ (c ∷ [])
  go .[] Eq.refl = Eq.refl

module _ {ℓA : Level} {A : TheoryTy ℓA tt} where

  -- absorbing the letter into the prefix
  Dl-absorb : (c : Alphabet) (w : ↓M tt)
    → literal c ⊗ Dl-string (w ++ (c ∷ [])) A ⊢ Dl-string w A
  Dl-absorb c w m (ms , e , (lc , (a , _))) =
    castEq {A = λ z → A (w ++ z)} e
      (castEq {A = λ z → A (w ++ (z ++ ms (suc zero)))} (Eq.sym lc)
        (castEq {A = A} (++-assocEq w (c ∷ []) (ms (suc zero))) a))

  -- ...and giving it back, which needs to know the letter is there
  Dl-absorb⁻ : (c : Alphabet) (w : ↓M tt)
    → (literal c ⊗ ⊤Ty) & Dl-string w A
    ⊢ literal c ⊗ Dl-string (w ++ (c ∷ [])) A
  Dl-absorb⁻ c w m ((ms , e , (lc , _)) , a) =
    ms , e ,
      (lc , (castEq {A = A} (Eq.sym (++-assocEq w (c ∷ []) (ms (suc zero))))
              (castEq {A = λ z → A (w ++ (z ++ ms (suc zero)))} lc
                (castEq {A = λ z → A (w ++ z)} (Eq.sym e) a))
            , tt*))
