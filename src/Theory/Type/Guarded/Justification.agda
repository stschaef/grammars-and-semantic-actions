-- Semantic justification for using guarded recursion
-- TODO how much of this is actually used?
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Guarded.Justification
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NO
import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit using (Unit* ; tt ; tt*)
open import Cubical.Relation.Nullary.Base using (Dec)
open import Cubical.Relation.Nullary.Base using (Discrete)
open import Cubical.Categories.Direct.Base using (WFOrder)

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Top.Base σeq V vs 𝒫
open import Theory.Type.Inductive.Base σeq V vs 𝒫
open import Theory.Type.Code.Container σeq V vs 𝒫 using (Split ; parts)
open import Theory.Type.Later.Indexed σeq V vs 𝒫
open import Theory.Type.Later.Tabulated σeq V vs 𝒫 using (Chain)
import Theory.Type.Later.Tabulated σeq V vs 𝒫 as Tab
open import Theory.Type.Guarded.Base σeq V vs 𝒫

private variable ℓA ℓB ℓR ℓW ℓX ℓ< : Level

module _ {X : Type ℓX} {xs : X → S} where
  module _ (O : IPtOrder xs ℓ<) where
    private
      module G = GuardedIndexed xs O
    open IPtOrder O using (_<_)

    löbFrom : {ℓA ℓR : Level} {R : Pt xs → Pt xs → Type ℓR}
      → (∀ {p q} → R p q → p < q)
      → (A : IFam xs ℓA) (isSetA : ∀ x m → isSet (A x m))
      → Löb R A
    löbFrom {ℓA = ℓA} {R = R} into A isSetA = record
      { ℓ▷ = G.ℓ▷ ℓA
      ; ▷ = L.▷
      ; next = L.next⊤
      ; app = λ r → L.▷app (into r)
      ; löb = L.löb
      ; löb-unfold = L.löb-unfold
      ; löb-uniq = λ φ t teq → L.löb-uniq φ t teq
      ; app-next = λ t r → refl
      }
      where module L = G.Fam▷ A isSetA

  module _ (O : IPtOrder xs ℓ<) (C : Chain xs O) where
    private
      module O = IPtOrder O
    open IPtOrder O using (_<_)

    module _ {ℓA ℓR : Level} {R : Pt xs → Pt xs → Type ℓR}
      (into : ∀ {p q} → R p q → p < q)
      (A : IFam xs ℓA) (isSetA : ∀ x m → isSet (A x m)) where
      private
        module T = Tab.Tabulated xs O C A isSetA

      löbMemo : Löb R A
      löbMemo = record
        { ℓ▷ = _
        ; ▷ = T.L.▷
        ; next = T.L.next⊤
        ; app = λ r → T.L.▷app (into r)
        ; löb = T.löbTab
        ; löb-unfold = λ φ x →
            (λ i → T.löbTab≡löb φ i x)
            ∙ T.L.löb-unfold φ x
            ∙ (λ i → φ x ∘⊢ T.L.next⊤ (T.löbTab≡löb φ (~ i)) x)
        ; löb-uniq = λ φ t teq → T.L.löb-uniq φ t teq ∙ sym (T.löbTab≡löb φ)
        ; app-next = λ t r → refl
        }

      -- memoising changes the cost, not the value
      löbMemo≡löbFrom : (φ : ∀ x → T.L.▷ x ⊢ A x)
        → Löb.löb löbMemo φ ≡ Löb.löb (löbFrom O into A isSetA) φ
      löbMemo≡löbFrom = T.löbTab≡löb

  -- ... and the order from a measure.  This is the *only* place a consumer's
  -- size argument has to go.
  löbByMeasure : (isSetX : isSet X) (W : WFOrder ℓW ℓ<)
    (meas : Pt xs → WFOrder.D W)
    {R : Pt xs → Pt xs → Type ℓR}
    → (∀ {p q} → R p q → WFOrder._<_ W (meas p) (meas q))
    → (A : IFam xs ℓA) (isSetA : ∀ x m → isSet (A x m))
    → Löb R A
  löbByMeasure isSetX W meas drops =
    löbFrom (irankOrder xs isSetX W meas) λ r → lift (drops r)

  -- The step vocabulary of the lexicographic guard, re-exported so that a
  -- consumer names it without naming an order.
  Lex : (size : (x : X) → ↓M (xs x) → ℕ) (rank : X → ℕ)
      → Pt xs → Pt xs → Type ℓ-zero
  Lex = LexStep xs

  decLex : (size : (x : X) → ↓M (xs x) → ℕ) (rank : X → ℕ)
         → ∀ p q → Dec (Lex size rank p q)
  decLex = decLexStep xs

  -- Löb along the lexicographic (input size, index rank) order: a step either
  -- shrinks the input or leaves its size alone and drops the rank.
  löbByLex : (isSetX : isSet X) (size : (x : X) → ↓M (xs x) → ℕ)
    (rank : X → ℕ) {R : Pt xs → Pt xs → Type ℓR}
    → (∀ {p q} → R p q → Lex size rank p q)
    → (A : IFam xs ℓA) (isSetA : ∀ x m → isSet (A x m))
    → Löb R A
  löbByLex isSetX size rank into =
    löbFrom (ilexOrder xs isSetX size rank) λ r → lift (into r)

  -- The same vocabulary against an order `W` on inputs rather than their
  -- size: a step either moves the input down in `W` -- takes a proper
  -- suffix -- or leaves it alone and drops the rank.
  Suffix : {ℓW ℓW< : Level} (W : WFOrder ℓW ℓW<)
    (inp : (x : X) → ↓M (xs x) → WFOrder.D W) (rank : X → ℕ)
    → Pt xs → Pt xs → Type (ℓ-max ℓW< ℓW)
  Suffix W inp rank = SuffixStep xs W inp rank

  decSuffix : {ℓW ℓW< : Level} (W : WFOrder ℓW ℓW<)
    (inp : (x : X) → ↓M (xs x) → WFOrder.D W) (rank : X → ℕ)
    → Discrete (WFOrder.D W) → (∀ a a' → Dec (WFOrder._<_ W a a'))
    → ∀ p q → Dec (Suffix W inp rank p q)
  decSuffix W inp rank = decSuffixStep xs W inp rank

  löbBySuffix : (isSetX : isSet X) {ℓW ℓW< : Level} (W : WFOrder ℓW ℓW<)
    (inp : (x : X) → ↓M (xs x) → WFOrder.D W) (rank : X → ℕ)
    {R : Pt xs → Pt xs → Type ℓR}
    → (∀ {p q} → R p q → Suffix W inp rank p q)
    → (A : IFam xs ℓA) (isSetA : ∀ x m → isSet (A x m))
    → Löb R A
  löbBySuffix isSetX W inp rank into =
    löbFrom (isuffixOrder xs W inp rank isSetX) λ r → lift (into r)

  -- Guardedness of a code: every recursive leaf sits strictly below the root.
  module _ (O : IPtOrder xs ℓ<) where
    open IPtOrder O using (_<_)

    Guard : {s : S} → Functor ℓA X xs s → ↓M s → Pt xs
          → Type (ℓ-max ℓX (ℓ-max ℓM ℓ<))
    Guard (k A) m root = Unit*
    Guard (Var x) m root = (x , m) < root
    Guard (⊕e Y G) m root = (y : Y) → Guard (G y) m root
    Guard (&e Y G) m root = (y : Y) → Guard (G y) m root
    Guard (G &e2 G') m root = Guard G m root × Guard G' m root
    Guard (⊗e o G) m root =
      (sp : Split o m) (a : arities σ o) → Guard (G a) (parts sp a) root
    Guard (⊗ᴰe o G) m root =
      (sp : Split o m) (a : arities σ o)
      → Guard (G (parts sp) a) (parts sp a) root

    module _ {A B : IFam xs ℓB} (root : Pt xs)
      (rec : (x : X) (m' : ↓M (xs x)) → (x , m') < root → A x m' → B x m')
      where
      mapG : {s : S} (F : Functor ℓA X xs s) (m : ↓M s)
        → Guard F m root → ⟦ F ⟧TheoryTy A m → ⟦ F ⟧TheoryTy B m
      mapG (k K) m g z = z
      mapG (Var x) m g z = lift (rec x m g (z .lower))
      mapG (⊕e Y G) m g (y , z) = y , mapG (G y) m (g y) z
      mapG (&e Y G) m g z = λ y → mapG (G y) m (g y) (z y)
      mapG (G &e2 G') m g (z , z') =
        mapG G m (g .fst) z , mapG G' m (g .snd) z'
      mapG (⊗e o G) m g (ms , e , h) =
        ms , e , λ a → mapG (G a) (ms a) (g (ms , e) a) (h a)
      mapG (⊗ᴰe o G) m g (ms , e , h) =
        ms , e , λ a → mapG (G ms a) (ms a) (g (ms , e) a) (h a)

    -- when the recursive call does not look at its guard, `mapG` *is* `map`
    private
      mapG≡map : {A B : IFam xs ℓB} (root : Pt xs) (f : ∀ x → A x ⊢ B x)
        {s : S} (F : Functor ℓA X xs s) (m : ↓M s) (g : Guard F m root)
        (z : ⟦ F ⟧TheoryTy A m)
        → mapG root (λ x m' _ → f x m') F m g z ≡ map F f m z
      mapG≡map root f (k K) m g z = refl
      mapG≡map root f (Var x) m g z = refl
      mapG≡map root f (⊕e Y G) m g (y , z) =
        cong (y ,_) (mapG≡map root f (G y) m (g y) z)
      mapG≡map root f (&e Y G) m g z =
        funExt λ y → mapG≡map root f (G y) m (g y) (z y)
      mapG≡map root f (G &e2 G') m g (z , z') =
        ≡-× (mapG≡map root f G m (g .fst) z)
            (mapG≡map root f G' m (g .snd) z')
      mapG≡map root f (⊗e o G) m g (ms , e , h) =
        cong (λ u → ms , e , u)
          (funExt λ a → mapG≡map root f (G a) (ms a) (g (ms , e) a) (h a))
      mapG≡map root f (⊗ᴰe o G) m g (ms , e , h) =
        cong (λ u → ms , e , u)
          (funExt λ a → mapG≡map root f (G ms a) (ms a) (g (ms , e) a) (h a))

    -- coalgebra + algebra + guardedness, by löb
    hylosFromGuard : (F : (x : X) → Functor ℓA X xs (xs x))
      → (∀ x m → Guard (F x) m (x , m)) → Hylos F
    hylosFromGuard F gF = record { hylo = hy ; hylo-unfold = hy-unfold }
      where
      module G = GuardedIndexed xs O

      -- the löb family is `A ⇒ B` pointwise, which is where `isSetB` is spent
      Fn : {ℓB : Level} (A B : IFam xs ℓB) → IFam xs ℓB
      Fn A B x m = A x m → B x m

      isSetFn : {ℓB : Level} {A B : IFam xs ℓB} → (∀ x m → isSet (B x m))
        → ∀ x m → isSet (Fn A B x m)
      isSetFn isSetB x m = isSetΠ λ _ → isSetB x m

      st : {ℓB : Level} {A B : IFam xs ℓB} (isSetB : ∀ x m → isSet (B x m))
        (c : ∀ x → A x ⊢ ⟦ F x ⟧TheoryTy A)
        (α : ∀ x → ⟦ F x ⟧TheoryTy B ⊢ B x)
        → ∀ x → G.Fam▷.▷ (Fn _ _) (isSetFn isSetB) x ⊢ Fn _ _ x
      st isSetB c α x m later a =
        α x m (mapG (x , m)
                (λ y m' lt → G.Fam▷.▷app (Fn _ _) (isSetFn isSetB) lt later)
                (F x) m (gF x m) (c x m a))

      hy : {ℓB : Level} {A B : IFam xs ℓB}
        → (∀ x m → isSet (B x m))
        → (c : ∀ x → A x ⊢ ⟦ F x ⟧TheoryTy A)
        → (α : ∀ x → ⟦ F x ⟧TheoryTy B ⊢ B x)
        → ∀ x → A x ⊢ B x
      hy isSetB c α x m a =
        G.Fam▷.löb (Fn _ _) (isSetFn isSetB) (st isSetB c α) x m tt a

      hy-unfold : {ℓB : Level} {A B : IFam xs ℓB}
        (isSetB : ∀ x m → isSet (B x m))
        (c : ∀ x → A x ⊢ ⟦ F x ⟧TheoryTy A)
        (α : ∀ x → ⟦ F x ⟧TheoryTy B ⊢ B x)
        → ∀ x → hy isSetB c α x ≡ α x ∘⊢ map (F x) (hy isSetB c α) ∘⊢ c x
      hy-unfold isSetB c α x = funExt λ m → funExt λ a →
        cong (λ e → e m tt a)
          (G.Fam▷.löb-unfold (Fn _ _) (isSetFn isSetB) (st isSetB c α) x)
        ∙ cong (α x m)
            (mapG≡map (x , m) (hy isSetB c α) (F x) m (gF x m) (c x m a))

  -- Löb by structural recursion on a fuel.
  --
  -- `löbByMeasure` builds `▷` from the direct category's downsets, so
  -- eliminating one applies a presheaf hom whose value comes from a match on
  -- an `Acc`, and the fixed point unfolds only up to a path.  Here `▷ x` *is*
  -- the type of eliminations along `R`, `app` is application, and the fixed
  -- point recurses on an ordinary numeral.  The bound proofs are carried and
  -- never matched, so nothing blocks: `löb φ x m tt` reduces to `φ`'s body on
  -- canonical input, which is what a `refl`-test needs.
  module _ {ℓA ℓR : Level} {R : Pt xs → Pt xs → Type ℓR}
    (A : IFam xs ℓA) (fuel : Pt xs → ℕ)
    (drops : ∀ {p q} → R p q → fuel p NO.< fuel q) where

    private
      ▷F : (x : X) → TheoryTy (ℓ-max ℓX (ℓ-max ℓM (ℓ-max ℓR ℓA))) (xs x)
      ▷F x m = (x' : X) (m' : ↓M (xs x')) → R (x' , m') (x , m) → A x' m'

      nextF : (∀ x → ⊤Ty ⊢ A x) → ∀ x → ⊤Ty ⊢ ▷F x
      nextF t x m _ x' m' r = t x' m' tt

      module _ (φ : ∀ x → ▷F x ⊢ A x) where
        -- the fuel is spent one unit per step, structurally
        go : (n : ℕ) (p : Pt xs) → fuel p NO.≤ n → A (p .fst) (p .snd)
        go zero p le = φ (p .fst) (p .snd) λ x' m' r →
          Empty.rec (NO.¬-<-zero (NO.≤-trans (drops r) le))
        go (suc n) p le = φ (p .fst) (p .snd) λ x' m' r →
          go n (x' , m') (NO.pred-≤-pred (NO.≤-trans (drops r) le))

        -- how much fuel was left over does not change the value
        go-irr : (n n' : ℕ) (p : Pt xs)
          (le : fuel p NO.≤ n) (le' : fuel p NO.≤ n') → go n p le ≡ go n' p le'
        go-irr zero zero p le le' = cong (φ (p .fst) (p .snd))
          (funExt λ x' → funExt λ m' → funExt λ r →
            Empty.rec (NO.¬-<-zero (NO.≤-trans (drops r) le)))
        go-irr zero (suc n') p le le' = cong (φ (p .fst) (p .snd))
          (funExt λ x' → funExt λ m' → funExt λ r →
            Empty.rec (NO.¬-<-zero (NO.≤-trans (drops r) le)))
        go-irr (suc n) zero p le le' = cong (φ (p .fst) (p .snd))
          (funExt λ x' → funExt λ m' → funExt λ r →
            Empty.rec (NO.¬-<-zero (NO.≤-trans (drops r) le')))
        go-irr (suc n) (suc n') p le le' = cong (φ (p .fst) (p .snd))
          (funExt λ x' → funExt λ m' → funExt λ r →
            go-irr n n' (x' , m') _ _)

        löbF : ∀ x → ⊤Ty ⊢ A x
        löbF x m _ = go (fuel (x , m)) (x , m) NO.≤-refl

        unf : (n : ℕ) (p : Pt xs) (le : fuel p NO.≤ n)
          → go n p le ≡ φ (p .fst) (p .snd) (nextF löbF (p .fst) (p .snd) tt)
        unf zero p le = cong (φ (p .fst) (p .snd))
          (funExt λ x' → funExt λ m' → funExt λ r →
            Empty.rec (NO.¬-<-zero (NO.≤-trans (drops r) le)))
        unf (suc n) p le = cong (φ (p .fst) (p .snd))
          (funExt λ x' → funExt λ m' → funExt λ r →
            go-irr n (fuel (x' , m')) (x' , m') _ NO.≤-refl)

        uniqAux : (t : ∀ x → ⊤Ty ⊢ A x)
          → (∀ x → t x ≡ φ x ∘⊢ nextF t x)
          → (n : ℕ) (p : Pt xs) (le : fuel p NO.≤ n)
          → t (p .fst) (p .snd) tt ≡ go n p le
        uniqAux t teq zero p le =
          (λ i → teq (p .fst) i (p .snd) tt)
          ∙ cong (φ (p .fst) (p .snd))
              (funExt λ x' → funExt λ m' → funExt λ r →
                Empty.rec (NO.¬-<-zero (NO.≤-trans (drops r) le)))
        uniqAux t teq (suc n) p le =
          (λ i → teq (p .fst) i (p .snd) tt)
          ∙ cong (φ (p .fst) (p .snd))
              (funExt λ x' → funExt λ m' → funExt λ r →
                uniqAux t teq n (x' , m') _)

    löbByFuel : Löb R A
    löbByFuel = record
      { ℓ▷ = _
      ; ▷ = ▷F
      ; next = nextF
      ; app = λ r β → β _ _ r
      ; löb = löbF
      ; löb-unfold = λ φ x → funExt λ m → funExt λ _ →
          unf φ (fuel (x , m)) (x , m) NO.≤-refl
      ; löb-uniq = λ φ t teq → funExt λ x → funExt λ m → funExt λ _ →
          uniqAux φ t teq (fuel (x , m)) (x , m) NO.≤-refl
      ; app-next = λ t r → refl
      }
