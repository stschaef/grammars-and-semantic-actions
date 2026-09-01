{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Type inference (pass 3): every binder is annotated, so inference alone
   suffices; the front end chains the passes, and `typed?` decides typing,
   unique by full annotation. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Examples.Theory.STLC.Typing where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Unit using (tt)

import Cubical.Data.Maybe as M
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no)
open import Cubical.Relation.Nullary.DiscreteEq
  using (discreteEqCong ; discreteEqCong2)

open import Examples.Theory.STLC.Scope

-- Pass 3: every binder is annotated, so inference alone suffices.

eqTy : ATy → ATy → Bool
eqTy Bo Bo = true
eqTy Na Na = true
eqTy (Ar a b) (Ar a' b') = eqTy a a' and eqTy b b'
  where open import Cubical.Data.Bool using (_and_)
eqTy (Pr a b) (Pr a' b') = eqTy a a' and eqTy b b'
  where open import Cubical.Data.Bool using (_and_)
eqTy (Li a) (Li a') = eqTy a a'
eqTy _ _ = false

private
  guard : Bool → ATy → M.Maybe ATy
  guard true A = M.just A
  guard false A = M.nothing

  lookΓ : List ATy → ℕ → M.Maybe ATy
  lookΓ [] i = M.nothing
  lookΓ (A ∷ Γ) zero = M.just A
  lookΓ (A ∷ Γ) (suc i) = lookΓ Γ i

infer : List ATy → BTm → M.Maybe ATy
infer Γ BTru = M.just Bo
infer Γ BFls = M.just Bo
infer Γ BZer = M.just Na
infer Γ (BVar i) = lookΓ Γ i
infer Γ (BSuc t) = infer Γ t >>= λ A → guard (eqTy A Na) Na
infer Γ (BIte c a b) =
  infer Γ c >>= λ C → infer Γ a >>= λ A → infer Γ b >>= λ B →
  guard (eqTy C Bo and eqTy A B) A
  where open import Cubical.Data.Bool using (_and_)
infer Γ (BLam A t) = infer (A ∷ Γ) t >>= λ B → M.just (Ar A B)
infer Γ (BApp f a) = infer Γ f >>= λ Fn → infer Γ a >>= λ A → app Fn A
  where
  app : ATy → ATy → M.Maybe ATy
  app (Ar A B) A' = guard (eqTy A A') B
  app _ _ = M.nothing
infer Γ (BPair a b) = infer Γ a >>= λ A → infer Γ b >>= λ B → M.just (Pr A B)
infer Γ (BFst t) = infer Γ t >>= fst'
  where
  fst' : ATy → M.Maybe ATy
  fst' (Pr A B) = M.just A
  fst' _ = M.nothing
infer Γ (BSnd t) = infer Γ t >>= snd'
  where
  snd' : ATy → M.Maybe ATy
  snd' (Pr A B) = M.just B
  snd' _ = M.nothing
infer Γ (BRec z s n) =
  infer Γ z >>= λ A → infer Γ s >>= λ Sx → infer Γ n >>= λ N →
  guard (eqTy Sx (Ar A A) and eqTy N Na) A
  where open import Cubical.Data.Bool using (_and_)
infer Γ (BNil A) = M.just (Li A)
infer Γ (BCons h t) =
  infer Γ h >>= λ A → infer Γ t >>= λ L → guard (eqTy L (Li A)) (Li A)
infer Γ (BFoldr f z xs) =
  infer Γ f >>= λ Fn → infer Γ z >>= λ B → infer Γ xs >>= λ L → go Fn B L
  where
  go : ATy → ATy → ATy → M.Maybe ATy
  go (Ar A (Ar B' B'')) B (Li A') =
    guard (eqTy A A' and (eqTy B B' and eqTy B B'')) B
    where open import Cubical.Data.Bool using (_and_)
  go _ _ _ = M.nothing
infer Γ (BLet t u) = infer Γ t >>= λ A → infer (A ∷ Γ) u

-- Front end: token list → parse tree → AST → scoped → typed.

astOf : (w : Src) → M.Maybe ATm
astOf w = go (parseTm w tt)
  where
  go : DecTy Term w → M.Maybe ATm
  go (Sum.inl t) = toTm (toTree Tm w t)
  go (Sum.inr _) = M.nothing

scopeOf : (w : Src) → M.Maybe BTm
scopeOf w = astOf w >>= scope []

tyOf : (w : Src) → M.Maybe ATy
tyOf w = scopeOf w >>= infer []

add-type : tyOf addSrc ≡ M.just (Ar Na (Ar Na Na))
add-type = refl

fib-type : tyOf fibSrc ≡ M.just Na
fib-type = refl

sum-type : tyOf sumSrc ≡ M.just Na
sum-type = refl

list-type : tyOf (`cons (`num 1) (`cons (`num 2) (`nil `nat))) ≡ M.just (Li Na)
list-type = refl

id-type : tyOf idSrc ≡ M.just (Ar Na Na)
id-type = refl

pair-type : tyOf (`pair `zero `true) ≡ M.just (Pr Na Bo)
pair-type = refl

-- the parser rejects: a type is not a term
parse-rejects : astOf `nat ≡ M.nothing
parse-rejects = refl

-- the scope checker rejects: `x` is free, though it parsed fine
unbound-parses : astOf (`var vx) ≡ M.just (Nm vx)
unbound-parses = refl

unbound-unscoped : scopeOf (`var vx) ≡ M.nothing
unbound-unscoped = refl

-- the typechecker rejects: `if` on a number, though it scoped fine
badIf : Src
badIf = `if `zero `then `zero `else `zero

isJust : {A : Type ℓ-zero} → M.Maybe A → Bool
isJust (M.just _) = true
isJust M.nothing = false

badIf-scopes : isJust (scopeOf badIf) ≡ true
badIf-scopes = refl

badIf-untyped : tyOf badIf ≡ M.nothing
badIf-untyped = refl

badSuc : tyOf (`suc `true) ≡ M.nothing
badSuc = refl

badApp : tyOf (idSrc `$ `true) ≡ M.nothing
badApp = refl

badCons : tyOf (`cons `true (`nil `nat)) ≡ M.nothing
badCons = refl

badFold : tyOf (`foldr idSrc `zero (`cons (`num 1) (`nil `nat))) ≡ M.nothing
badFold = refl


-- Pass 3 as a decision: full annotation makes typing unique, so a mismatch
-- with the inferred type refutes, by `unique`.

open import Cubical.Data.Sigma using (Σ-syntax ; _×_)

_≟ty_ : (A B : ATy) → (A Eq.≡ B) Sum.⊎ ((A Eq.≡ B) → Empty.⊥)
Bo ≟ty Bo = Sum.inl Eq.refl
Na ≟ty Na = Sum.inl Eq.refl
Ar a b ≟ty Ar a' b' = discreteEqCong2 Ar
  (λ where Eq.refl → Eq.refl) (λ where Eq.refl → Eq.refl)
  (a ≟ty a') (b ≟ty b')
Pr a b ≟ty Pr a' b' = discreteEqCong2 Pr
  (λ where Eq.refl → Eq.refl) (λ where Eq.refl → Eq.refl)
  (a ≟ty a') (b ≟ty b')
Li a ≟ty Li a' = discreteEqCong Li (λ where Eq.refl → Eq.refl) (a ≟ty a')
Bo ≟ty Na = Sum.inr λ ()
Bo ≟ty Ar _ _ = Sum.inr λ ()
Bo ≟ty Pr _ _ = Sum.inr λ ()
Bo ≟ty Li _ = Sum.inr λ ()
Na ≟ty Bo = Sum.inr λ ()
Na ≟ty Ar _ _ = Sum.inr λ ()
Na ≟ty Pr _ _ = Sum.inr λ ()
Na ≟ty Li _ = Sum.inr λ ()
Ar _ _ ≟ty Bo = Sum.inr λ ()
Ar _ _ ≟ty Na = Sum.inr λ ()
Ar _ _ ≟ty Pr _ _ = Sum.inr λ ()
Ar _ _ ≟ty Li _ = Sum.inr λ ()
Pr _ _ ≟ty Bo = Sum.inr λ ()
Pr _ _ ≟ty Na = Sum.inr λ ()
Pr _ _ ≟ty Ar _ _ = Sum.inr λ ()
Pr _ _ ≟ty Li _ = Sum.inr λ ()
Li _ ≟ty Bo = Sum.inr λ ()
Li _ ≟ty Na = Sum.inr λ ()
Li _ ≟ty Ar _ _ = Sum.inr λ ()
Li _ ≟ty Pr _ _ = Sum.inr λ ()

Ctx : Type ℓ-zero
Ctx = List (Tok × ATy)

-- lookup as a function: shadowing automatic, deterministic by construction
lookupC : Ctx → Tok → M.Maybe ATy
lookupC [] x = M.nothing
lookupC ((y , B) ∷ Γ) x = go (y ≟T x)
  where
  go : (y Eq.≡ x) Sum.⊎ ((y Eq.≡ x) → Empty.⊥) → M.Maybe ATy
  go (Sum.inl Eq.refl) = M.just B
  go (Sum.inr _) = lookupC Γ x

data Typed : Ctx → ATm → ATy → Type ℓ-zero where
  tTru : {Γ : Ctx} → Typed Γ Tru Bo
  tFls : {Γ : Ctx} → Typed Γ Fls Bo
  tZer : {Γ : Ctx} → Typed Γ Zer Na
  tNil : {Γ : Ctx} {A : ATy} → Typed Γ (Nil A) (Li A)
  tNm  : {Γ : Ctx} {x : Tok} {A : ATy}
    → lookupC Γ x Eq.≡ M.just A → Typed Γ (Nm x) A
  tSuc : {Γ : Ctx} {t : ATm} → Typed Γ t Na → Typed Γ (Suc t) Na
  tFst : {Γ : Ctx} {t : ATm} {A B : ATy}
    → Typed Γ t (Pr A B) → Typed Γ (Fst t) A
  tSnd : {Γ : Ctx} {t : ATm} {A B : ATy}
    → Typed Γ t (Pr A B) → Typed Γ (Snd t) B
  tApp : {Γ : Ctx} {f a : ATm} {A B : ATy}
    → Typed Γ f (Ar A B) → Typed Γ a A → Typed Γ (App f a) B
  tPair : {Γ : Ctx} {a b : ATm} {A B : ATy}
    → Typed Γ a A → Typed Γ b B → Typed Γ (Pair a b) (Pr A B)
  tCons : {Γ : Ctx} {h t : ATm} {A : ATy}
    → Typed Γ h A → Typed Γ t (Li A) → Typed Γ (Cons h t) (Li A)
  tIte : {Γ : Ctx} {c a b : ATm} {A : ATy}
    → Typed Γ c Bo → Typed Γ a A → Typed Γ b A → Typed Γ (Ite c a b) A
  tRec : {Γ : Ctx} {z s n : ATm} {A : ATy}
    → Typed Γ z A → Typed Γ s (Ar A A) → Typed Γ n Na → Typed Γ (Rec z s n) A
  tFoldr : {Γ : Ctx} {f z xs : ATm} {A B : ATy}
    → Typed Γ f (Ar A (Ar B B)) → Typed Γ z B → Typed Γ xs (Li A)
    → Typed Γ (Foldr f z xs) B
  tLam : {Γ : Ctx} {x : Tok} {A : ATy} {t : ATm} {B : ATy}
    → Typed ((x , A) ∷ Γ) t B → Typed Γ (Lam x A t) (Ar A B)
  tLet : {Γ : Ctx} {x : Tok} {t u : ATm} {A B : ATy}
    → Typed Γ t A → Typed ((x , A) ∷ Γ) u B → Typed Γ (Let x t u) B

justInj : {A B : ATy} → M.just A Eq.≡ M.just B → A Eq.≡ B
justInj Eq.refl = Eq.refl

uniqueᶜ : {x : Tok} {A B : ATy} {Γ : Ctx}
  → lookupC Γ x Eq.≡ M.just A → lookupC Γ x Eq.≡ M.just B → A Eq.≡ B
uniqueᶜ p q = justInj (Eq.sym p Eq.∙ q)

unique : {Γ : Ctx} {t : ATm} {A B : ATy} → Typed Γ t A → Typed Γ t B → A Eq.≡ B
unique tTru tTru = Eq.refl
unique tFls tFls = Eq.refl
unique tZer tZer = Eq.refl
unique tNil tNil = Eq.refl
unique (tNm p) (tNm q) = uniqueᶜ p q
unique (tSuc _) (tSuc _) = Eq.refl
unique (tFst p) (tFst q) = go (unique p q)
  where
  go : {A B A' B' : ATy} → Pr A B Eq.≡ Pr A' B' → A Eq.≡ A'
  go Eq.refl = Eq.refl
unique (tSnd p) (tSnd q) = go (unique p q)
  where
  go : {A B A' B' : ATy} → Pr A B Eq.≡ Pr A' B' → B Eq.≡ B'
  go Eq.refl = Eq.refl
unique (tApp p _) (tApp q _) = go (unique p q)
  where
  go : {A B A' B' : ATy} → Ar A B Eq.≡ Ar A' B' → B Eq.≡ B'
  go Eq.refl = Eq.refl
unique (tPair p p') (tPair q q') = go (unique p q) (unique p' q')
  where
  go : {A A' B B' : ATy} → A Eq.≡ A' → B Eq.≡ B' → Pr A B Eq.≡ Pr A' B'
  go Eq.refl Eq.refl = Eq.refl
unique (tCons p _) (tCons q _) = go (unique p q)
  where
  go : {A A' : ATy} → A Eq.≡ A' → Li A Eq.≡ Li A'
  go Eq.refl = Eq.refl
unique (tIte _ p _) (tIte _ q _) = unique p q
unique (tRec p _ _) (tRec q _ _) = unique p q
unique (tFoldr _ p _) (tFoldr _ q _) = unique p q
unique (tLam p) (tLam q) = go (unique p q)
  where
  go : {A B B' : ATy} → B Eq.≡ B' → Ar A B Eq.≡ Ar A B'
  go Eq.refl = Eq.refl
unique (tLet p p') (tLet q q') = go (unique p q) p' q'
  where
  go : {Γ : Ctx} {x : Tok} {u : ATm} {A A' B B' : ATy} → A Eq.≡ A'
     → Typed ((x , A) ∷ Γ) u B → Typed ((x , A') ∷ Γ) u B' → B Eq.≡ B'
  go Eq.refl p' q' = unique p' q'

data ArV : ATy → Type ℓ-zero where
  isAr : (A B : ATy) → ArV (Ar A B)
  noAr : {C : ATy} → ((A B : ATy) → C Eq.≡ Ar A B → Empty.⊥) → ArV C

arV : (C : ATy) → ArV C
arV Bo = noAr λ A B ()
arV Na = noAr λ A B ()
arV (Ar A B) = isAr A B
arV (Pr _ _) = noAr λ A B ()
arV (Li _) = noAr λ A B ()

data PrV : ATy → Type ℓ-zero where
  isPr : (A B : ATy) → PrV (Pr A B)
  noPr : {C : ATy} → ((A B : ATy) → C Eq.≡ Pr A B → Empty.⊥) → PrV C

prV : (C : ATy) → PrV C
prV Bo = noPr λ A B ()
prV Na = noPr λ A B ()
prV (Ar _ _) = noPr λ A B ()
prV (Pr A B) = isPr A B
prV (Li _) = noPr λ A B ()

private
  arDom : {A B A' B' : ATy} → Ar A B Eq.≡ Ar A' B' → A Eq.≡ A'
  arDom Eq.refl = Eq.refl

  arCod : {A B A' B' : ATy} → Ar A B Eq.≡ Ar A' B' → B Eq.≡ B'
  arCod Eq.refl = Eq.refl

  liC : {A A' : ATy} → A Eq.≡ A' → Li A Eq.≡ Li A'
  liC Eq.refl = Eq.refl

  arC : {A B B' : ATy} → B Eq.≡ B' → Ar A B Eq.≡ Ar A B'
  arC Eq.refl = Eq.refl

  arBoth : {B₀ B : ATy} → B₀ Eq.≡ B → Ar B₀ B₀ Eq.≡ Ar B B
  arBoth Eq.refl = Eq.refl

Ty? : Ctx → ATm → Type ℓ-zero
Ty? Γ t = Σ[ A ∈ ATy ] Typed Γ t A

typed? : (Γ : Ctx) (t : ATm) → Dec (Ty? Γ t)
typed? Γ Tru = yes (Bo , tTru)
typed? Γ Fls = yes (Bo , tFls)
typed? Γ Zer = yes (Na , tZer)
typed? Γ (Nil A) = yes (Li A , tNil)
typed? Γ (Nm x) = go (lookupC Γ x) Eq.refl
  where
  bad : {A : ATy} → M.nothing Eq.≡ M.just A → Empty.⊥
  bad ()

  go : (r : M.Maybe ATy) → lookupC Γ x Eq.≡ r → Dec (Ty? Γ (Nm x))
  go (M.just A) e = yes (A , tNm e)
  go M.nothing e = no λ where (A , tNm p) → bad (Eq.sym e Eq.∙ p)
typed? Γ (Suc t) = go (typed? Γ t)
  where
  go : Dec (Ty? Γ t) → Dec (Ty? Γ (Suc t))
  go (no ¬p) = no λ where (_ , tSuc d) → ¬p (Na , d)
  go (yes (A , d)) = chk (A ≟ty Na)
    where
    chk : (A Eq.≡ Na) Sum.⊎ ((A Eq.≡ Na) → Empty.⊥) → Dec (Ty? Γ (Suc t))
    chk (Sum.inl Eq.refl) = yes (Na , tSuc d)
    chk (Sum.inr ne) = no λ where (_ , tSuc d') → ne (unique d d')
typed? Γ (Fst t) = go (typed? Γ t)
  where
  go : Dec (Ty? Γ t) → Dec (Ty? Γ (Fst t))
  go (no ¬p) = no λ where (_ , tFst d) → ¬p (_ , d)
  go (yes (C , d)) = chk (prV C)
    where
    chk : PrV C → Dec (Ty? Γ (Fst t))
    chk (isPr A B) = yes (A , tFst d)
    chk (noPr ne) = no λ where
      (_ , tFst {A = A} {B = B} d') → ne A B (unique d d')
typed? Γ (Snd t) = go (typed? Γ t)
  where
  go : Dec (Ty? Γ t) → Dec (Ty? Γ (Snd t))
  go (no ¬p) = no λ where (_ , tSnd d) → ¬p (_ , d)
  go (yes (C , d)) = chk (prV C)
    where
    chk : PrV C → Dec (Ty? Γ (Snd t))
    chk (isPr A B) = yes (B , tSnd d)
    chk (noPr ne) = no λ where
      (_ , tSnd {A = A} {B = B} d') → ne A B (unique d d')
typed? Γ (Pair a b) = go (typed? Γ a) (typed? Γ b)
  where
  go : Dec (Ty? Γ a) → Dec (Ty? Γ b) → Dec (Ty? Γ (Pair a b))
  go (no ¬p) _ = no λ where (_ , tPair d _) → ¬p (_ , d)
  go _ (no ¬q) = no λ where (_ , tPair _ d) → ¬q (_ , d)
  go (yes (A , da)) (yes (B , db)) = yes (Pr A B , tPair da db)
typed? Γ (App f a) = go (typed? Γ f) (typed? Γ a)
  where
  go : Dec (Ty? Γ f) → Dec (Ty? Γ a) → Dec (Ty? Γ (App f a))
  go (no ¬p) _ = no λ where (_ , tApp d _) → ¬p (_ , d)
  go _ (no ¬q) = no λ where (_ , tApp _ d) → ¬q (_ , d)
  go (yes (C , df)) (yes (A' , da)) = chk (arV C)
    where
    chk : ArV C → Dec (Ty? Γ (App f a))
    chk (noAr ne) = no λ where
      (_ , tApp {A = A''} {B = B''} d' _) → ne A'' B'' (unique df d')
    chk (isAr A B) = chk2 (A ≟ty A')
      where
      chk2 : (A Eq.≡ A') Sum.⊎ ((A Eq.≡ A') → Empty.⊥) → Dec (Ty? Γ (App f a))
      chk2 (Sum.inl Eq.refl) = yes (B , tApp df da)
      chk2 (Sum.inr ne) = no λ where
        (_ , tApp d' e') →
          ne (arDom (unique df d') Eq.∙ Eq.sym (unique da e'))
typed? Γ (Cons h t) = go (typed? Γ h) (typed? Γ t)
  where
  go : Dec (Ty? Γ h) → Dec (Ty? Γ t) → Dec (Ty? Γ (Cons h t))
  go (no ¬p) _ = no λ where (_ , tCons d _) → ¬p (_ , d)
  go _ (no ¬q) = no λ where (_ , tCons _ d) → ¬q (_ , d)
  go (yes (A , dh)) (yes (L , dt)) = chk (L ≟ty Li A)
    where
    chk : (L Eq.≡ Li A) Sum.⊎ ((L Eq.≡ Li A) → Empty.⊥) → Dec (Ty? Γ (Cons h t))
    chk (Sum.inl Eq.refl) = yes (Li A , tCons dh dt)
    chk (Sum.inr ne) = no λ where
      (_ , tCons dh' dt') →
        ne (unique dt dt' Eq.∙ liC (Eq.sym (unique dh dh')))
typed? Γ (Ite c a b) = go (typed? Γ c) (typed? Γ a) (typed? Γ b)
  where
  go : Dec (Ty? Γ c) → Dec (Ty? Γ a) → Dec (Ty? Γ b) → Dec (Ty? Γ (Ite c a b))
  go (no ¬p) _ _ = no λ where (_ , tIte d _ _) → ¬p (_ , d)
  go _ (no ¬q) _ = no λ where (_ , tIte _ d _) → ¬q (_ , d)
  go _ _ (no ¬r) = no λ where (_ , tIte _ _ d) → ¬r (_ , d)
  go (yes (C , dc)) (yes (A , da)) (yes (B , db)) = chk (C ≟ty Bo) (A ≟ty B)
    where
    chk : (C Eq.≡ Bo) Sum.⊎ ((C Eq.≡ Bo) → Empty.⊥)
        → (A Eq.≡ B) Sum.⊎ ((A Eq.≡ B) → Empty.⊥) → Dec (Ty? Γ (Ite c a b))
    chk (Sum.inr ne) _ = no λ where (_ , tIte d' _ _) → ne (unique dc d')
    chk _ (Sum.inr ne) = no λ where
      (_ , tIte _ d' e') → ne (unique da d' Eq.∙ Eq.sym (unique db e'))
    chk (Sum.inl Eq.refl) (Sum.inl Eq.refl) = yes (A , tIte dc da db)
typed? Γ (Rec z s n) = go (typed? Γ z) (typed? Γ s) (typed? Γ n)
  where
  go : Dec (Ty? Γ z) → Dec (Ty? Γ s) → Dec (Ty? Γ n) → Dec (Ty? Γ (Rec z s n))
  go (no ¬p) _ _ = no λ where (_ , tRec d _ _) → ¬p (_ , d)
  go _ (no ¬q) _ = no λ where (_ , tRec _ d _) → ¬q (_ , d)
  go _ _ (no ¬r) = no λ where (_ , tRec _ _ d) → ¬r (_ , d)
  go (yes (A , dz)) (yes (Sy , ds)) (yes (N , dn)) =
    chk (Sy ≟ty Ar A A) (N ≟ty Na)
    where
    chk : (Sy Eq.≡ Ar A A) Sum.⊎ ((Sy Eq.≡ Ar A A) → Empty.⊥)
        → (N Eq.≡ Na) Sum.⊎ ((N Eq.≡ Na) → Empty.⊥) → Dec (Ty? Γ (Rec z s n))
    chk (Sum.inr ne) _ = no λ where
      (_ , tRec d' e' _) →
        ne (unique ds e' Eq.∙ arBoth (Eq.sym (unique dz d')))
    chk _ (Sum.inr ne) = no λ where (_ , tRec _ _ d') → ne (unique dn d')
    chk (Sum.inl Eq.refl) (Sum.inl Eq.refl) = yes (A , tRec dz ds dn)
typed? Γ (Lam x A t) = go (typed? ((x , A) ∷ Γ) t)
  where
  go : Dec (Ty? ((x , A) ∷ Γ) t) → Dec (Ty? Γ (Lam x A t))
  go (no ¬p) = no λ where (_ , tLam d) → ¬p (_ , d)
  go (yes (B , d)) = yes (Ar A B , tLam d)
typed? Γ (Foldr f z xs) = go (typed? Γ f) (typed? Γ z) (typed? Γ xs)
  where
  go : Dec (Ty? Γ f) → Dec (Ty? Γ z) → Dec (Ty? Γ xs)
     → Dec (Ty? Γ (Foldr f z xs))
  go (no ¬p) _ _ = no λ where (_ , tFoldr d _ _) → ¬p (_ , d)
  go _ (no ¬q) _ = no λ where (_ , tFoldr _ d _) → ¬q (_ , d)
  go _ _ (no ¬r) = no λ where (_ , tFoldr _ _ d) → ¬r (_ , d)
  go (yes (C , df)) (yes (B , dz)) (yes (L , dxs)) = chk (arV C)
    where
    chk : ArV C → Dec (Ty? Γ (Foldr f z xs))
    chk (noAr ne) = no λ where
      (_ , tFoldr {A = A₀} {B = B₀} d' _ _) → ne A₀ (Ar B₀ B₀) (unique df d')
    chk (isAr A rest) = chk2 (rest ≟ty Ar B B) (L ≟ty Li A)
      where
      chk2 : (rest Eq.≡ Ar B B) Sum.⊎ ((rest Eq.≡ Ar B B) → Empty.⊥)
           → (L Eq.≡ Li A) Sum.⊎ ((L Eq.≡ Li A) → Empty.⊥)
           → Dec (Ty? Γ (Foldr f z xs))
      chk2 (Sum.inr ne) _ = no λ where
        (_ , tFoldr d' e' _) →
          ne (arCod (unique df d') Eq.∙ arBoth (Eq.sym (unique dz e')))
      chk2 _ (Sum.inr ne) = no λ where
        (_ , tFoldr d' _ e') →
          ne (unique dxs e' Eq.∙ liC (Eq.sym (arDom (unique df d'))))
      chk2 (Sum.inl Eq.refl) (Sum.inl Eq.refl) = yes (B , tFoldr df dz dxs)
typed? Γ (Let x t u) = go (typed? Γ t)
  where
  go : Dec (Ty? Γ t) → Dec (Ty? Γ (Let x t u))
  go (no ¬p) = no λ where (_ , tLet d _) → ¬p (_ , d)
  go (yes (A , dt)) = go2 (typed? ((x , A) ∷ Γ) u)
    where
    shift : {A' B' : ATy} → A Eq.≡ A' → Typed ((x , A') ∷ Γ) u B'
          → Ty? ((x , A) ∷ Γ) u
    shift Eq.refl d = _ , d

    go2 : Dec (Ty? ((x , A) ∷ Γ) u) → Dec (Ty? Γ (Let x t u))
    go2 (no ¬q) = no λ where
      (_ , tLet d' e') → ¬q (shift (unique dt d') e')
    go2 (yes (B , du)) = yes (B , tLet dt du)

isYesD : {A : Type ℓ-zero} → Dec A → Bool
isYesD (yes _) = true
isYesD (no _) = false

theD : {A : Type ℓ-zero} (d : Dec A) → isYesD d Eq.≡ true → A
theD (yes a) _ = a
theD (no _) ()

theNotD : {A : Type ℓ-zero} (d : Dec A) → isYesD d Eq.≡ false → A → Empty.⊥
theNotD (no ¬a) _ = ¬a
theNotD (yes _) ()

private
  orTru : M.Maybe ATm → ATm
  orTru (M.just t) = t
  orTru M.nothing = Tru

fibAST sumAST addAST badIfAST : ATm
fibAST = orTru (astOf fibSrc)
sumAST = orTru (astOf sumSrc)
addAST = orTru (astOf addSrc)
badIfAST = orTru (astOf badIf)

fib-scoped : Scoped [] fibAST
fib-scoped = theD (scoped? [] fibAST) Eq.refl

sum-scoped : Scoped [] sumAST
sum-scoped = theD (scoped? [] sumAST) Eq.refl

unbound-refuted : Scoped [] (Nm vx) → Empty.⊥
unbound-refuted = theNotD (scoped? [] (Nm vx)) Eq.refl

bound-scoped : Scoped [] (Lam vx Na (Nm vx))
bound-scoped = theD (scoped? [] (Lam vx Na (Nm vx))) Eq.refl

fib-typed : Ty? [] fibAST
fib-typed = theD (typed? [] fibAST) Eq.refl

fib-typed-nat : fst fib-typed ≡ Na
fib-typed-nat = refl

sum-typed : Ty? [] sumAST
sum-typed = theD (typed? [] sumAST) Eq.refl

sum-typed-nat : fst sum-typed ≡ Na
sum-typed-nat = refl

add-typed : Ty? [] addAST
add-typed = theD (typed? [] addAST) Eq.refl

add-typed-arr : fst add-typed ≡ Ar Na (Ar Na Na)
add-typed-arr = refl

badIf-refuted : Ty? [] badIfAST → Empty.⊥
badIf-refuted = theNotD (typed? [] badIfAST) Eq.refl

badSuc-refuted : Ty? [] (Suc Tru) → Empty.⊥
badSuc-refuted = theNotD (typed? [] (Suc Tru)) Eq.refl

badApp-refuted : Ty? [] (App (Lam vx Na (Nm vx)) Tru) → Empty.⊥
badApp-refuted = theNotD (typed? [] (App (Lam vx Na (Nm vx)) Tru)) Eq.refl

badCons-refuted : Ty? [] (Cons Tru (Nil Na)) → Empty.⊥
badCons-refuted = theNotD (typed? [] (Cons Tru (Nil Na))) Eq.refl

badFst-refuted : Ty? [] (Fst Zer) → Empty.⊥
badFst-refuted = theNotD (typed? [] (Fst Zer)) Eq.refl
