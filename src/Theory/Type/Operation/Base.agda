-- Lifting an operation from a theory to a type constructor
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Type.Operation.Base
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Unit using (Unit* ; tt* ; isPropUnit*)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
import Cubical.Data.Equality as Eq

open import Cubical.WildCat.LocallySmall.Base

open import Theory.Base σeq V vs 𝒫

open WildCatNotation
open WildCatIso

private variable ℓA ℓB : Level

private
  isPropValEq : ∀ {s} {x y : ↓M s} → isProp (x Eq.≡ y)
  isPropValEq {s} =
    isOfHLevelRetractFromIso 1 (invIso Eq.PathIsoEq) (M .fst s .snd _ _)

sup : (n : ℕ) → (Fin n → Level) → Level
sup zero ℓs = ℓ-zero
sup (suc n) ℓs = ℓ-max (ℓs zero) (sup n (λ i → ℓs (suc i)))

Args : (n : ℕ) (ℓs : Fin n → Level) → (Fin n → S)
     → Type (ℓ-max ℓM (ℓ-suc (sup n ℓs)))
Args zero ℓs ss = Unit*
Args (suc n) ℓs ss =
  TheoryTy (ℓs zero) (ss zero) × Args n (λ i → ℓs (suc i)) (λ i → ss (suc i))

Elems : (n : ℕ) (ℓs : Fin n → Level) (ss : Fin n → S)
     → Args n ℓs ss → ((i : Fin n) → ↓M (ss i)) → Type (sup n ℓs)
Elems zero ℓs ss As ms = Unit*
Elems (suc n) ℓs ss (A , As) ms =
  A (ms zero) × Elems n (λ i → ℓs (suc i)) (λ i → ss (suc i)) As (λ i → ms (suc i))

⊗[_][_] : (o : σ .ops) (ℓs : arities σ o → Level)
     → Args (σ .arity o) ℓs (σ .sortOf o)
     → TheoryTy (ℓ-max ℓM (sup (σ .arity o) ℓs)) (σ .resultSort o)
⊗[ o ][ ℓs ] As m =
  Σ[ ms ∈ interpIn o ↓M ]
    (M .snd .fst o ms Eq.≡ m) × Elems (σ .arity o) ℓs (σ .sortOf o) As ms

same-inputs : (o : σ .ops) (ℓs : arities σ o → Level)
  (As : Args (σ .arity o) ℓs (σ .sortOf o)) {x y : ↓M (σ .resultSort o)}
  → ⊗[ o ][ ℓs ] As x → ⊗[ o ][ ℓs ] As y → Type ℓM
same-inputs o ℓs As p q = p .fst ≡ q .fst

same-elements : (o : σ .ops) (ℓs : arities σ o → Level)
  (As : Args (σ .arity o) ℓs (σ .sortOf o)) {x y : ↓M (σ .resultSort o)}
  (p : ⊗[ o ][ ℓs ] As x) (q : ⊗[ o ][ ℓs ] As y)
  → same-inputs o ℓs As p q → Type (sup (σ .arity o) ℓs)
same-elements o ℓs As p q ms≡ =
  PathP (λ j → Elems (σ .arity o) ℓs (σ .sortOf o) As (ms≡ j))
    (p .snd .snd) (q .snd .snd)

⊗PathP : (o : σ .ops) (ℓs : arities σ o → Level)
  (As : Args (σ .arity o) ℓs (σ .sortOf o))
  {z : I → ↓M (σ .resultSort o)}
  {p : ⊗[ o ][ ℓs ] As (z i0)} {q : ⊗[ o ][ ℓs ] As (z i1)}
  (ms≡ : same-inputs o ℓs As p q)
  → same-elements o ℓs As p q ms≡
  → PathP (λ j → ⊗[ o ][ ℓs ] As (z j)) p q
⊗PathP o ℓs As ms≡ xs≡ = ΣPathP (ms≡ , ΣPathP
  (isProp→PathP (λ j → isPropValEq) _ _ , xs≡))

⊗≡ : (o : σ .ops) (ℓs : arities σ o → Level)
  (As : Args (σ .arity o) ℓs (σ .sortOf o)) {z : ↓M (σ .resultSort o)}
  (p q : ⊗[ o ][ ℓs ] As z) (ms≡ : same-inputs o ℓs As p q)
  → same-elements o ℓs As p q ms≡ → p ≡ q
⊗≡ o ℓs As p q ms≡ xs≡ = ⊗PathP o ℓs As ms≡ xs≡

⊗ᵘ[_] : (o : σ .ops)
     → interpIn o (TheoryTy ℓA)
     → TheoryTy (ℓ-max ℓM ℓA) (σ .resultSort o)
⊗ᵘ[ o ] A m =
  Σ[ ms ∈ interpIn o ↓M ]
    (M .snd .fst o ms Eq.≡ m) × ((a : arities σ o) → A a (ms a))

⊗ᵘ-intro : {o : σ .ops} (A : interpIn o (TheoryTy ℓA))
  (ms : interpIn o ↓M) → ((a : arities σ o) → A a (ms a))
  → ⊗ᵘ[ o ] A (op o ms)
⊗ᵘ-intro A ms xs = ms , Eq.refl , xs

⊗ᵘ-elim : {o : σ .ops} (A : interpIn o (TheoryTy ℓA))
  {C : TheoryTy ℓB (σ .resultSort o)}
  → ({ms : interpIn o ↓M} → ((a : arities σ o) → A a (ms a)) → C (op o ms))
  → ⊗ᵘ[ o ] A ⊢ C
⊗ᵘ-elim A f _ (ms , Eq.refl , xs) = f xs

⊗-intro : {o : σ .ops} {ℓs : arities σ o → Level}
  (As : Args (σ .arity o) ℓs (σ .sortOf o))
  (ms : interpIn o ↓M)
  → Elems (σ .arity o) ℓs (σ .sortOf o) As ms
  → ⊗[ o ][ ℓs ] As (op o ms)
⊗-intro As ms xs = ms , Eq.refl , xs

⊗-elim : {o : σ .ops} {ℓs : arities σ o → Level}
  (As : Args (σ .arity o) ℓs (σ .sortOf o))
  {C : TheoryTy ℓB (σ .resultSort o)}
  → ({ms : interpIn o ↓M}
      → Elems (σ .arity o) ℓs (σ .sortOf o) As ms → C (op o ms))
  → ⊗[ o ][ ℓs ] As ⊢ C
⊗-elim As f _ (ms , Eq.refl , xs) = f xs

-- `⊗-elim`'s computing sibling.  It *projects* the splitting instead of
-- matching it, and hands both the decomposition and its proof to `f`, which
-- rebuilds the slots over that same splitting.  Nothing here forces `e`.
--
-- That matters whenever the model is a quotient: there a splitting is
-- routinely a `pathToEq` of a path and never reduces to `Eq.refl`, so
-- `⊗-elim` (and `∀ᵒ-intro`, which matches the same proof) block, while this
-- does not.  Measured on `Bags/Quicksort/Tests`: matching costs >7min where
-- projecting costs 3.3s.
⊗-overSplit : {o : σ .ops} {ℓs ℓs' : arities σ o → Level}
  {As : Args (σ .arity o) ℓs (σ .sortOf o)}
  {As' : Args (σ .arity o) ℓs' (σ .sortOf o)}
  (m : ↓M (σ .resultSort o))
  → ((ms : interpIn o ↓M) → op o ms Eq.≡ m
     → Elems (σ .arity o) ℓs (σ .sortOf o) As ms
     → Elems (σ .arity o) ℓs' (σ .sortOf o) As' ms)
  → ⊗[ o ][ ℓs ] As m → ⊗[ o ][ ℓs' ] As' m
⊗-overSplit m f t = t .fst , t .snd .fst , f (t .fst) (t .snd .fst) (t .snd .snd)

-- The same, with a value carried alongside: this is how a delayed hypothesis
-- reaches the slots.
⊗&-overSplit : {o : σ .ops} {ℓs ℓs' : arities σ o → Level}
  {As : Args (σ .arity o) ℓs (σ .sortOf o)}
  {As' : Args (σ .arity o) ℓs' (σ .sortOf o)}
  {D : TheoryTy ℓB (σ .resultSort o)}
  → ((m : ↓M (σ .resultSort o)) (ms : interpIn o ↓M) → op o ms Eq.≡ m
     → Elems (σ .arity o) ℓs (σ .sortOf o) As ms → D m
     → Elems (σ .arity o) ℓs' (σ .sortOf o) As' ms)
  → (λ m → ⊗[ o ][ ℓs ] As m × D m) ⊢ ⊗[ o ][ ℓs' ] As'
⊗&-overSplit f m (t , d) =
  t .fst , t .snd .fst , f m (t .fst) (t .snd .fst) (t .snd .snd) d

⊗map : (o : σ .ops)
     {A : interpIn o (TheoryTy ℓA)}
     {B : interpIn o (TheoryTy ℓB)}
     → (∀ a → A a ⊢ B a)
     → ⊗ᵘ[ o ] A ⊢ ⊗ᵘ[ o ] B
⊗map o f m (m⃗ , e , g) = m⃗ , e , λ a → f a (m⃗ a) (g a)

⊗ᶠ : {n : ℕ} {ws : Fin n → S} {s : S}
   → (Val ws → ↓M s) → (ℓs : Fin n → Level) → Args n ℓs ws
   → TheoryTy (ℓ-max ℓM (sup n ℓs)) s
⊗ᶠ {n = n} {ws = ws} f ℓs As m =
  Σ[ ρ ∈ Val ws ] ((f ρ Eq.≡ m) × Elems n ℓs ws As ρ)

⟪_⟫[_] : {n : ℕ} {ws : Fin n → S} {s : S}
    → Tm σ (Fin n) ws s → (ℓs : Fin n → Level) → Args n ℓs ws
    → TheoryTy _ s
⟪ t ⟫[ ℓs ] = ⊗ᶠ (λ ρ → eval ρ t) ℓs

argAt : (n : ℕ) (ℓs : Fin n → Level) (ws : Fin n → S)
      → Args n ℓs ws → (i : Fin n) → TheoryTy (ℓs i) (ws i)
argAt (suc n) ℓs ws (A , As) zero = A
argAt (suc n) ℓs ws (A , As) (suc i) =
  argAt n (λ j → ℓs (suc j)) (λ j → ws (suc j)) As i

elemAt : (n : ℕ) (ℓs : Fin n → Level) (ws : Fin n → S)
         (As : Args n ℓs ws) (ms : (i : Fin n) → ↓M (ws i))
       → Elems n ℓs ws As ms → (i : Fin n) → argAt n ℓs ws As i (ms i)
elemAt (suc n) ℓs ws (A , As) ms (x , xs) zero = x
elemAt (suc n) ℓs ws (A , As) ms (x , xs) (suc i) =
  elemAt n (λ j → ℓs (suc j)) (λ j → ws (suc j)) As (λ j → ms (suc j)) xs i

mapElems : (n : ℕ) (ℓs : Fin n → Level) (ks : Fin n → Level)
  (ws : Fin n → S) (As : Args n ℓs ws) (Bs : Args n ks ws)
  → ((i : Fin n) → argAt n ℓs ws As i ⊢ argAt n ks ws Bs i)
  → (ms : (i : Fin n) → ↓M (ws i))
  → Elems n ℓs ws As ms → Elems n ks ws Bs ms
mapElems zero ℓs ks ws tt* tt* f ms tt* = tt*
mapElems (suc n) ℓs ks ws (A , As) (B , Bs) f ms (a , as) =
  f zero (ms zero) a ,
  mapElems n (λ i → ℓs (suc i)) (λ i → ks (suc i))
    (λ i → ws (suc i)) As Bs (λ i → f (suc i)) (λ i → ms (suc i)) as

-- Map an operation convolution with independently varying input levels.
⊗map[_][_] : (o : σ .ops) (ℓs : arities σ o → Level)
  (ks : arities σ o → Level)
  {As : Args (σ .arity o) ℓs (σ .sortOf o)}
  {Bs : Args (σ .arity o) ks (σ .sortOf o)}
  → ((i : arities σ o) → argAt (σ .arity o) ℓs (σ .sortOf o) As i
                       ⊢ argAt (σ .arity o) ks (σ .sortOf o) Bs i)
  → ⊗[ o ][ ℓs ] As ⊢ ⊗[ o ][ ks ] Bs
⊗map[ o ][ ℓs ] ks {As = As} {Bs = Bs} f m (ms , e , as) =
  ms , e , mapElems (σ .arity o) ℓs ks (σ .sortOf o) As Bs f ms as

private
  satEq : (e : σeq .eqns) (ρ : Val (σeq .varSort e))
    → eval ρ (σeq .lhs e) Eq.≡ eval ρ (σeq .rhs e)
  satEq = satStrict

eqn→Iso :
  (e : σeq .eqns) (ℓs : vars σeq e → Level)
  (m : Args (σeq .varCount e) ℓs (σeq .varSort e)) →
  ⟪ σeq .lhs e ⟫[ ℓs ] m ≅ ⟪ σeq .rhs e ⟫[ ℓs ] m
eqn→Iso e ℓs m .fun x (ρ , p , xs) = ρ , Eq.sym (satEq e ρ) Eq.∙ p , xs
eqn→Iso e ℓs m .inv x (ρ , p , xs) = ρ , satEq e ρ Eq.∙ p , xs
eqn→Iso e ℓs m .sec = funExt λ x → funExt λ q → λ i →
  q .fst ,
  isPropValEq
    (Eq.sym (satEq e (q .fst)) Eq.∙ (satEq e (q .fst) Eq.∙ q .snd .fst))
    (q .snd .fst) i ,
  q .snd .snd
eqn→Iso e ℓs m .ret = funExt λ x → funExt λ q → λ i →
  q .fst ,
  isPropValEq
    (satEq e (q .fst) Eq.∙ (Eq.sym (satEq e (q .fst)) Eq.∙ q .snd .fst))
    (q .snd .fst) i ,
  q .snd .snd

eqn→fun :
  (e : σeq .eqns) (ℓs : vars σeq e → Level)
  (m : Args (σeq .varCount e) ℓs (σeq .varSort e)) →
  ⟪ σeq .lhs e ⟫[ ℓs ] m ⊢ ⟪ σeq .rhs e ⟫[ ℓs ] m
eqn→fun e ℓs m = eqn→Iso e ℓs m .fun

eqn→inv :
  (e : σeq .eqns) (ℓs : vars σeq e → Level)
  (m : Args (σeq .varCount e) ℓs (σeq .varSort e)) →
  ⟪ σeq .rhs e ⟫[ ℓs ] m ⊢ ⟪ σeq .lhs e ⟫[ ℓs ] m
eqn→inv e ℓs m = eqn→Iso e ℓs m .inv

⊗⌈⌉Iso : (o : σ .ops) (ms : interpIn o ↓M) (m : ↓M (σ .resultSort o))
  → Iso (⊗ᵘ[ o ] (λ a → ⌈ ms a ⌉) m) (⌈ M .snd .fst o ms ⌉ m)
⊗⌈⌉Iso o ms m .Iso.fun (ms' , e , as) =
  Eq.sym e Eq.∙
  Eq.pathToEq (cong (M .snd .fst o) (funExt λ a → Eq.eqToPath (as a)))
⊗⌈⌉Iso o ms m .Iso.inv p = ms , Eq.sym p , λ a → Eq.refl
⊗⌈⌉Iso o ms m .Iso.sec p = isPropValEq _ _
⊗⌈⌉Iso o ms m .Iso.ret (ms' , e , as) =
  ΣPathP (funExt (λ a → sym (Eq.eqToPath (as a)))
    , isProp→PathP (λ _ → isProp× isPropValEq (isPropΠ λ _ → isPropValEq)) _ _)

-- The convolution of a term that is a bare variable is the slot it names.
unVar : {n : ℕ} {ws : Fin n → S} {ℓs : Fin n → Level}
  {As : Args n ℓs ws} (v : Fin n)
  → ⟪ var v ⟫[ ℓs ] As ⊢ argAt n ℓs ws As v
unVar {n = n} {ws = ws} {ℓs = ℓs} {As = As} v m (ρ , Eq.refl , h) =
  elemAt n ℓs ws As ρ h v
