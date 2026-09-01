{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Parse tree → AST (pass 1), then scope checking (pass 2): names become
   de Bruijn indices; also pass 2 as a decision, by inversion on `Scoped`. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Examples.Theory.STLC.Scope where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)

open import Examples.Theory.STLC.Parser public

-- Pass 1: parse tree → AST.

import Cubical.Data.Maybe as M

_>>=_ : {A B : Type ℓ-zero} → M.Maybe A → (A → M.Maybe B) → M.Maybe B
M.just a >>= f = f a
M.nothing >>= f = M.nothing

data ATy : Type ℓ-zero where
  Bo Na : ATy
  Ar Pr : ATy → ATy → ATy
  Li : ATy → ATy

data ATm : Type ℓ-zero where
  Tru Fls Zer : ATm
  Ite Rec Foldr : ATm → ATm → ATm → ATm
  Suc Fst Snd : ATm → ATm
  App Pair Cons : ATm → ATm → ATm
  Nil : ATy → ATm
  Lam : Tok → ATy → ATm → ATm
  Let : Tok → ATm → ATm → ATm
  Nm : Tok → ATm

toTy : Tree → M.Maybe ATy
toTy (node (tk kbool) []) = M.just Bo
toTy (node (tk knat) []) = M.just Na
toTy (node (tk karr) (a ∷ b ∷ [])) = toTy a >>= λ A → toTy b >>= λ B → M.just (Ar A B)
toTy (node (tk kprod) (a ∷ b ∷ [])) = toTy a >>= λ A → toTy b >>= λ B → M.just (Pr A B)
toTy (node (tk klist) (a ∷ [])) = toTy a >>= λ A → M.just (Li A)
toTy _ = M.nothing

toName : Tree → M.Maybe Tok
toName (node (tk c) []) = M.just c
toName _ = M.nothing

toTm : Tree → M.Maybe ATm
toTm (node (tk ktrue) []) = M.just Tru
toTm (node (tk kfalse) []) = M.just Fls
toTm (node (tk kzero) []) = M.just Zer
toTm (node (tk kif) (c ∷ a ∷ b ∷ [])) =
  toTm c >>= λ C → toTm a >>= λ A → toTm b >>= λ B → M.just (Ite C A B)
toTm (node (tk ksuc) (t ∷ [])) = toTm t >>= λ T → M.just (Suc T)
toTm (node (tk knatrec) (z ∷ s ∷ n ∷ [])) =
  toTm z >>= λ Z → toTm s >>= λ Sx → toTm n >>= λ N → M.just (Rec Z Sx N)
toTm (node (tk klam) (v ∷ a ∷ t ∷ [])) =
  toName v >>= λ x → toTy a >>= λ A → toTm t >>= λ T → M.just (Lam x A T)
toTm (node (tk kapp) (f ∷ a ∷ [])) =
  toTm f >>= λ Fn → toTm a >>= λ A → M.just (App Fn A)
toTm (node (tk kpair) (a ∷ b ∷ [])) =
  toTm a >>= λ A → toTm b >>= λ B → M.just (Pair A B)
toTm (node (tk kfst) (t ∷ [])) = toTm t >>= λ T → M.just (Fst T)
toTm (node (tk ksnd) (t ∷ [])) = toTm t >>= λ T → M.just (Snd T)
toTm (node (tk knil) (a ∷ [])) = toTy a >>= λ A → M.just (Nil A)
toTm (node (tk kcons) (h ∷ t ∷ [])) =
  toTm h >>= λ H → toTm t >>= λ T → M.just (Cons H T)
toTm (node (tk kfoldr) (f ∷ z ∷ xs ∷ [])) =
  toTm f >>= λ Fn → toTm z >>= λ Z → toTm xs >>= λ Xs → M.just (Foldr Fn Z Xs)
toTm (node (tk klet) (v ∷ t ∷ u ∷ [])) =
  toName v >>= λ x → toTm t >>= λ T → toTm u >>= λ U → M.just (Let x T U)
toTm (node (tk vf) []) = M.just (Nm vf)
toTm (node (tk vg) []) = M.just (Nm vg)
toTm (node (tk vn) []) = M.just (Nm vn)
toTm (node (tk vx) []) = M.just (Nm vx)
toTm (node (tk vxs) []) = M.just (Nm vxs)
toTm _ = M.nothing

-- Pass 2: scope checking; names become de Bruijn indices.

data BTm : Type ℓ-zero where
  BTru BFls BZer : BTm
  BIte BRec BFoldr : BTm → BTm → BTm → BTm
  BSuc BFst BSnd : BTm → BTm
  BApp BPair BCons : BTm → BTm → BTm
  BNil : ATy → BTm
  BLam : ATy → BTm → BTm
  BLet : BTm → BTm → BTm
  BVar : ℕ → BTm

eqTok : Tok → Tok → Bool
eqTok a b = Sum.rec (λ _ → true) (λ _ → false) (a ≟T b)

idx : List Tok → Tok → M.Maybe ℕ
idx [] y = M.nothing
idx (x ∷ Γ) y with eqTok x y
... | true = M.just 0
... | false = idx Γ y >>= λ i → M.just (suc i)

scope : List Tok → ATm → M.Maybe BTm
scope Γ Tru = M.just BTru
scope Γ Fls = M.just BFls
scope Γ Zer = M.just BZer
scope Γ (Ite c a b) =
  scope Γ c >>= λ C → scope Γ a >>= λ A → scope Γ b >>= λ B → M.just (BIte C A B)
scope Γ (Rec z s n) =
  scope Γ z >>= λ Z → scope Γ s >>= λ Sx → scope Γ n >>= λ N → M.just (BRec Z Sx N)
scope Γ (Foldr f z xs) =
  scope Γ f >>= λ Fn → scope Γ z >>= λ Z → scope Γ xs >>= λ Xs →
  M.just (BFoldr Fn Z Xs)
scope Γ (Suc t) = scope Γ t >>= λ T → M.just (BSuc T)
scope Γ (Fst t) = scope Γ t >>= λ T → M.just (BFst T)
scope Γ (Snd t) = scope Γ t >>= λ T → M.just (BSnd T)
scope Γ (App f a) = scope Γ f >>= λ Fn → scope Γ a >>= λ A → M.just (BApp Fn A)
scope Γ (Pair a b) = scope Γ a >>= λ A → scope Γ b >>= λ B → M.just (BPair A B)
scope Γ (Cons h t) = scope Γ h >>= λ H → scope Γ t >>= λ T → M.just (BCons H T)
scope Γ (Nil A) = M.just (BNil A)
scope Γ (Lam x A t) = scope (x ∷ Γ) t >>= λ T → M.just (BLam A T)
scope Γ (Let x t u) =
  scope Γ t >>= λ T → scope (x ∷ Γ) u >>= λ U → M.just (BLet T U)
scope Γ (Nm x) = idx Γ x >>= λ i → M.just (BVar i)


-- Pass 2 as a decision: derivation or refutation, by inversion on `Scoped`.

open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no)

infix 4 _∈_

data _∈_ (x : Tok) : List Tok → Type ℓ-zero where
  here  : {Γ : List Tok} → x ∈ (x ∷ Γ)
  there : {y : Tok} {Γ : List Tok} → x ∈ Γ → x ∈ (y ∷ Γ)

_∈?_ : (x : Tok) (Γ : List Tok) → Dec (x ∈ Γ)
x ∈? [] = no λ ()
x ∈? (y ∷ Γ) = hd (y ≟T x)
  where
  rest : Dec (x ∈ Γ) → ((x Eq.≡ y) → Empty.⊥) → Dec (x ∈ (y ∷ Γ))
  rest (yes i) ne = yes (there i)
  rest (no ¬i) ne = no λ where
    here → ne Eq.refl
    (there i) → ¬i i

  hd : (y Eq.≡ x) Sum.⊎ ((y Eq.≡ x) → Empty.⊥) → Dec (x ∈ (y ∷ Γ))
  hd (Sum.inl Eq.refl) = yes here
  hd (Sum.inr ne) = rest (x ∈? Γ) λ where Eq.refl → ne Eq.refl

data Scoped : List Tok → ATm → Type ℓ-zero where
  sTru : {Γ : List Tok} → Scoped Γ Tru
  sFls : {Γ : List Tok} → Scoped Γ Fls
  sZer : {Γ : List Tok} → Scoped Γ Zer
  sNil : {Γ : List Tok} {A : ATy} → Scoped Γ (Nil A)
  sNm  : {Γ : List Tok} {x : Tok} → x ∈ Γ → Scoped Γ (Nm x)
  sSuc : {Γ : List Tok} {t : ATm} → Scoped Γ t → Scoped Γ (Suc t)
  sFst : {Γ : List Tok} {t : ATm} → Scoped Γ t → Scoped Γ (Fst t)
  sSnd : {Γ : List Tok} {t : ATm} → Scoped Γ t → Scoped Γ (Snd t)
  sApp : {Γ : List Tok} {f a : ATm} → Scoped Γ f → Scoped Γ a → Scoped Γ (App f a)
  sPair : {Γ : List Tok} {a b : ATm} → Scoped Γ a → Scoped Γ b → Scoped Γ (Pair a b)
  sCons : {Γ : List Tok} {h t : ATm} → Scoped Γ h → Scoped Γ t → Scoped Γ (Cons h t)
  sIte : {Γ : List Tok} {c a b : ATm}
    → Scoped Γ c → Scoped Γ a → Scoped Γ b → Scoped Γ (Ite c a b)
  sRec : {Γ : List Tok} {z s n : ATm}
    → Scoped Γ z → Scoped Γ s → Scoped Γ n → Scoped Γ (Rec z s n)
  sFoldr : {Γ : List Tok} {f z xs : ATm}
    → Scoped Γ f → Scoped Γ z → Scoped Γ xs → Scoped Γ (Foldr f z xs)
  sLam : {Γ : List Tok} {x : Tok} {A : ATy} {t : ATm}
    → Scoped (x ∷ Γ) t → Scoped Γ (Lam x A t)
  sLet : {Γ : List Tok} {x : Tok} {t u : ATm}
    → Scoped Γ t → Scoped (x ∷ Γ) u → Scoped Γ (Let x t u)

private
  d1 : {A C : Type ℓ-zero} → Dec A → (A → C) → (C → A) → Dec C
  d1 (yes a) f g = yes (f a)
  d1 (no ¬a) f g = no λ c → ¬a (g c)

  d2 : {A B C : Type ℓ-zero} → Dec A → Dec B → (A → B → C)
     → (C → A) → (C → B) → Dec C
  d2 (yes a) (yes b) f g h = yes (f a b)
  d2 (no ¬a) _ f g h = no λ c → ¬a (g c)
  d2 _ (no ¬b) f g h = no λ c → ¬b (h c)

  d3 : {A B C D : Type ℓ-zero} → Dec A → Dec B → Dec C → (A → B → C → D)
     → (D → A) → (D → B) → (D → C) → Dec D
  d3 (yes a) (yes b) (yes c) f g h i = yes (f a b c)
  d3 (no ¬a) _ _ f g h i = no λ d → ¬a (g d)
  d3 _ (no ¬b) _ f g h i = no λ d → ¬b (h d)
  d3 _ _ (no ¬c) f g h i = no λ d → ¬c (i d)

scoped? : (Γ : List Tok) (t : ATm) → Dec (Scoped Γ t)
scoped? Γ Tru = yes sTru
scoped? Γ Fls = yes sFls
scoped? Γ Zer = yes sZer
scoped? Γ (Nil A) = yes sNil
scoped? Γ (Nm x) = d1 (x ∈? Γ) sNm λ where (sNm i) → i
scoped? Γ (Suc t) = d1 (scoped? Γ t) sSuc λ where (sSuc p) → p
scoped? Γ (Fst t) = d1 (scoped? Γ t) sFst λ where (sFst p) → p
scoped? Γ (Snd t) = d1 (scoped? Γ t) sSnd λ where (sSnd p) → p
scoped? Γ (App f a) = d2 (scoped? Γ f) (scoped? Γ a) sApp
  (λ where (sApp p q) → p) (λ where (sApp p q) → q)
scoped? Γ (Pair a b) = d2 (scoped? Γ a) (scoped? Γ b) sPair
  (λ where (sPair p q) → p) (λ where (sPair p q) → q)
scoped? Γ (Cons h t) = d2 (scoped? Γ h) (scoped? Γ t) sCons
  (λ where (sCons p q) → p) (λ where (sCons p q) → q)
scoped? Γ (Ite c a b) = d3 (scoped? Γ c) (scoped? Γ a) (scoped? Γ b) sIte
  (λ where (sIte p q r) → p) (λ where (sIte p q r) → q) (λ where (sIte p q r) → r)
scoped? Γ (Rec z s n) = d3 (scoped? Γ z) (scoped? Γ s) (scoped? Γ n) sRec
  (λ where (sRec p q r) → p) (λ where (sRec p q r) → q) (λ where (sRec p q r) → r)
scoped? Γ (Foldr f z xs) = d3 (scoped? Γ f) (scoped? Γ z) (scoped? Γ xs) sFoldr
  (λ where (sFoldr p q r) → p) (λ where (sFoldr p q r) → q)
  (λ where (sFoldr p q r) → r)
scoped? Γ (Lam x A t) = d1 (scoped? (x ∷ Γ) t) sLam λ where (sLam p) → p
scoped? Γ (Let x t u) = d2 (scoped? Γ t) (scoped? (x ∷ Γ) u) sLet
  (λ where (sLet p q) → p) (λ where (sLet p q) → q)
