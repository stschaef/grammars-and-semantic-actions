{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Bracket-matching cover: classify a word by the token that follows the
   match of its opening `(` -- a lookahead class no finite-state device gives. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Examples.Theory.Combinator.Bracket where

open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; ++-assoc)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Relation.Nullary.DiscreteEq
  using (discreteEqMaybe ; discreteEqCong)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.FinData using () renaming (zero to fz ; suc to fs)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; _×_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)
open import Cubical.Foundations.Prelude using (Lift ; lift)

data Tok : Type where
  lp rp vid cm ar dot : Tok

_≟T_ : (x y : Tok) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
lp ≟T lp = Sum.inl Eq.refl
lp ≟T rp = Sum.inr λ ()
lp ≟T vid = Sum.inr λ ()
lp ≟T cm = Sum.inr λ ()
lp ≟T ar = Sum.inr λ ()
lp ≟T dot = Sum.inr λ ()
rp ≟T lp = Sum.inr λ ()
rp ≟T rp = Sum.inl Eq.refl
rp ≟T vid = Sum.inr λ ()
rp ≟T cm = Sum.inr λ ()
rp ≟T ar = Sum.inr λ ()
rp ≟T dot = Sum.inr λ ()
vid ≟T lp = Sum.inr λ ()
vid ≟T rp = Sum.inr λ ()
vid ≟T vid = Sum.inl Eq.refl
vid ≟T cm = Sum.inr λ ()
vid ≟T ar = Sum.inr λ ()
vid ≟T dot = Sum.inr λ ()
cm ≟T lp = Sum.inr λ ()
cm ≟T rp = Sum.inr λ ()
cm ≟T vid = Sum.inr λ ()
cm ≟T cm = Sum.inl Eq.refl
cm ≟T ar = Sum.inr λ ()
cm ≟T dot = Sum.inr λ ()
ar ≟T lp = Sum.inr λ ()
ar ≟T rp = Sum.inr λ ()
ar ≟T vid = Sum.inr λ ()
ar ≟T cm = Sum.inr λ ()
ar ≟T ar = Sum.inl Eq.refl
ar ≟T dot = Sum.inr λ ()
dot ≟T lp = Sum.inr λ ()
dot ≟T rp = Sum.inr λ ()
dot ≟T vid = Sum.inr λ ()
dot ≟T cm = Sum.inr λ ()
dot ≟T ar = Sum.inr λ ()
dot ≟T dot = Sum.inl Eq.refl

-- `after t`: opens with a `(` whose match is followed by `t`;  `noMatch`:
-- opens with a `(` that never closes;  `headed c`: does not open with a
-- `(`;  `blank`: the empty word.
data Cls : Type where
  after   : Maybe Tok → Cls
  noMatch : Cls
  headed  : Tok → Cls
  blank   : Cls

decMTok : (x y : Maybe Tok) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
decMTok = discreteEqMaybe _≟T_

decCls : (x y : Cls) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
decCls (after s) (after t) =
  discreteEqCong after (λ where Eq.refl → Eq.refl) (decMTok s t)
decCls (headed c) (headed d) =
  discreteEqCong headed (λ where Eq.refl → Eq.refl) (c ≟T d)
decCls noMatch noMatch = Sum.inl Eq.refl
decCls blank blank = Sum.inl Eq.refl
decCls (after s) noMatch = Sum.inr λ ()
decCls (after s) (headed d) = Sum.inr λ ()
decCls (after s) blank = Sum.inr λ ()
decCls noMatch (after t) = Sum.inr λ ()
decCls noMatch (headed d) = Sum.inr λ ()
decCls noMatch blank = Sum.inr λ ()
decCls (headed c) (after t) = Sum.inr λ ()
decCls (headed c) noMatch = Sum.inr λ ()
decCls (headed c) blank = Sum.inr λ ()
decCls blank (after t) = Sum.inr λ ()
decCls blank noMatch = Sum.inr λ ()
decCls blank (headed d) = Sum.inr λ ()

-- `cls` stays private (as `Lookahead/Window`'s `win`): it justifies the
-- cover; no client may reason with it.
private
  headOf : List Tok → Maybe Tok
  headOf [] = nothing
  headOf (t ∷ _) = just t

  -- Token is split before depth, so a non-bracket letter reduces without
  -- knowing `d` -- which transparency needs.
  chase : ℕ → List Tok → Cls
  chase d [] = noMatch
  chase d (lp ∷ m) = chase (suc d) m
  chase d (vid ∷ m) = chase d m
  chase d (cm ∷ m) = chase d m
  chase d (ar ∷ m) = chase d m
  chase d (dot ∷ m) = chase d m
  chase zero (rp ∷ m) = after (headOf m)
  chase (suc d) (rp ∷ m) = chase d m

  cls : List Tok → Cls
  cls [] = blank
  cls (lp ∷ m) = chase zero m
  cls (rp ∷ m) = headed rp
  cls (vid ∷ m) = headed vid
  cls (cm ∷ m) = headed cm
  cls (ar ∷ m) = headed ar
  cls (dot ∷ m) = headed dot

Transparent : List Tok → Type
Transparent m = (d : ℕ) (x : List Tok) → chase d (m ++ x) Eq.≡ chase d x

transp-nil : Transparent []
transp-nil d x = Eq.refl

transp-vid : {m : List Tok} → Transparent m → Transparent (vid ∷ m)
transp-vid t d x = t d x

transp-cm : {m : List Tok} → Transparent m → Transparent (cm ∷ m)
transp-cm t d x = t d x

transp-ar : {m : List Tok} → Transparent m → Transparent (ar ∷ m)
transp-ar t d x = t d x

transp-dot : {m : List Tok} → Transparent m → Transparent (dot ∷ m)
transp-dot t d x = t d x

-- `Closing q`: `q` ends by closing one bracket more than it opens
-- (`ClosingS`: the same, one level deeper).
Closing : List Tok → Type
Closing q = (y : List Tok) → chase zero (q ++ y) Eq.≡ after (headOf y)

ClosingS : List Tok → Type
ClosingS q = (d : ℕ) (y : List Tok) → chase (suc d) (q ++ y) Eq.≡ chase d y

closing-one : Closing (vid ∷ (rp ∷ []))
closing-one y = Eq.refl

closingS-one : ClosingS (vid ∷ (rp ∷ []))
closingS-one d y = Eq.refl

closing-cons : {q : List Tok} → Closing q → Closing (vid ∷ (cm ∷ q))
closing-cons cq y = cq y

closingS-cons : {q : List Tok} → ClosingS q → ClosingS (vid ∷ (cm ∷ q))
closingS-cons cq d y = cq d y

transp-open : {q n : List Tok} → ClosingS q → Transparent n
  → Transparent (lp ∷ (q ++ n))
transp-open {q = q} {n = n} cq tn d x =
  Eq.transport (λ z → chase (suc d) z Eq.≡ chase d x)
    (Eq.sym (Eq.pathToEq (++-assoc q n x)))
    (cq d (n ++ x) Eq.∙ tn d x)

transp-wrap : {m n : List Tok} → Transparent m → Transparent n
  → Transparent (lp ∷ (m ++ (rp ∷ n)))
transp-wrap {m = m} {n = n} tm tn d x =
  Eq.transport (λ z → chase (suc d) z Eq.≡ chase d x)
    (Eq.sym (Eq.pathToEq (++-assoc m (rp ∷ n) x)))
    (tm (suc d) (rp ∷ (n ++ x)) Eq.∙ tn d x)

cls-open : {p : List Tok} → Transparent p → (t : Tok) (y : List Tok)
  → cls (lp ∷ (p ++ (rp ∷ (t ∷ y)))) Eq.≡ after (just t)
cls-open {p = p} tp t y = tp zero (rp ∷ (t ∷ y))

cls-close : {q : List Tok} → Closing q → (t : Tok) (y : List Tok)
  → cls (lp ∷ (q ++ (t ∷ y))) Eq.≡ after (just t)
cls-close cq t y = cq (t ∷ y)

cls-vid : (y : List Tok) → cls (vid ∷ y) Eq.≡ headed vid
cls-vid y = Eq.refl

open import Theory.Instances.Monoid.Types Tok _≟T_
  hiding (Maybe ; just ; nothing)
open import Theory.Type.Decidable.Route
  MonEqns Tok (λ _ → tt) listPresentation

-- Parts are the fibres of `cls`: no syntactic part exists short of a
-- balanced-string `μ` plus match-uniqueness, so the classifier IS the part.
-- `total`/`disjoint` are one line each; every `into` is a parse-tree induction.

BT : Cls → TheoryTy ℓM tt
BT i m = Lift ℓM (cls m Eq.≡ i)

bracketCover : Cover Cls BT
bracketCover .total m _ = cls m , lift Eq.refl
bracketCover .disjoint i i' ne m (lift p , lift p') =
  Empty.rec (ne (Eq.sym p Eq.∙ p'))

decClsEq : DiscreteEq Cls
decClsEq = decCls

-- Every tensor decomposition happens here; a grammar using this cover
-- composes these and never splits a word itself.

NotBr : Tok → Type
NotBr lp = Empty.⊥
NotBr rp = Empty.⊥
NotBr vid = Unit
NotBr cm = Unit
NotBr ar = Unit
NotBr dot = Unit

TranspG ClosG : TheoryTy ℓ-zero tt
TranspG m = Transparent m
ClosG m = Closing m × ClosingS m

private
  skipTr : (c : Tok) → NotBr c → {v : List Tok}
    → Transparent v → Transparent (c ∷ v)
  skipTr vid _ t = transp-vid t
  skipTr cm _ t = transp-cm t
  skipTr ar _ t = transp-ar t
  skipTr dot _ t = transp-dot t

  skipCl : (c : Tok) → NotBr c → {v : List Tok}
    → Closing v × ClosingS v → Closing (c ∷ v) × ClosingS (c ∷ v)
  skipCl vid _ (a , b) = (λ y → a y) , (λ d y → b d y)
  skipCl cm _ (a , b) = (λ y → a y) , (λ d y → b d y)
  skipCl ar _ (a , b) = (λ y → a y) , (λ d y → b d y)
  skipCl dot _ (a , b) = (λ y → a y) , (λ d y → b d y)

tr-lit : (c : Tok) → NotBr c → literal c ⊢ TranspG
tr-lit c nb m e = Eq.transport Transparent (Eq.sym e) (skipTr c nb transp-nil)

tr-skip : (c : Tok) → NotBr c → literal c ⊗ TranspG ⊢ TranspG
tr-skip c nb m (ms , e , (lc , (t , tt*))) =
  go (ms fz) (ms (fs fz)) lc e t
  where
  go : (u v : List Tok) → u Eq.≡ (c ∷ []) → (u ++ v) Eq.≡ m
     → Transparent v → Transparent m
  go .(c ∷ []) v Eq.refl Eq.refl tv = skipTr c nb tv

cl-rp : literal rp ⊢ ClosG
cl-rp m e =
  Eq.transport (λ z → Closing z × ClosingS z) (Eq.sym e)
    ((λ y → Eq.refl) , (λ d y → Eq.refl))

cl-skip : (c : Tok) → NotBr c → literal c ⊗ ClosG ⊢ ClosG
cl-skip c nb m (ms , e , (lc , (t , tt*))) =
  go (ms fz) (ms (fs fz)) lc e t
  where
  go : (u v : List Tok) → u Eq.≡ (c ∷ []) → (u ++ v) Eq.≡ m
     → Closing v × ClosingS v → Closing m × ClosingS m
  go .(c ∷ []) v Eq.refl Eq.refl cv = skipCl c nb cv

tr-open : literal lp ⊗ (ClosG ⊗ TranspG) ⊢ TranspG
tr-open m (ms , e , (lc , (rest , tt*))) =
  go (ms fz) (ms (fs fz)) lc e rest
  where
  go : (u v : List Tok) → u Eq.≡ (lp ∷ []) → (u ++ v) Eq.≡ m
     → (ClosG ⊗ TranspG) v → Transparent m
  go .(lp ∷ []) v Eq.refl Eq.refl (ns , f , (cq , (tn , tt*))) =
    go2 (ns fz) (ns (fs fz)) f cq tn
    where
    go2 : (a b : List Tok) → (a ++ b) Eq.≡ v
        → Closing a × ClosingS a → Transparent b → Transparent (lp ∷ v)
    go2 a b Eq.refl ca tb = transp-open (ca .snd) tb

tr-wrap : literal lp ⊗ (TranspG ⊗ (literal rp ⊗ TranspG)) ⊢ TranspG
tr-wrap m (ms , e , (lc , (rest , tt*))) =
  go (ms fz) (ms (fs fz)) lc e rest
  where
  go : (u v : List Tok) → u Eq.≡ (lp ∷ []) → (u ++ v) Eq.≡ m
     → (TranspG ⊗ (literal rp ⊗ TranspG)) v → Transparent m
  go .(lp ∷ []) v Eq.refl Eq.refl (ns , f , (ta , (rest2 , tt*))) =
    go2 (ns fz) (ns (fs fz)) f ta rest2
    where
    go2 : (a b : List Tok) → (a ++ b) Eq.≡ v → Transparent a
        → (literal rp ⊗ TranspG) b → Transparent (lp ∷ v)
    go2 a b Eq.refl ta2 (os , f2 , (lr , (tb , tt*))) =
      go3 (os fz) (os (fs fz)) lr f2 tb
      where
      go3 : (c d : List Tok) → c Eq.≡ (rp ∷ []) → (c ++ d) Eq.≡ b
          → Transparent d → Transparent (lp ∷ (a ++ b))
      go3 .(rp ∷ []) d Eq.refl Eq.refl td = transp-wrap ta2 td

bt-open : (t : Tok)
  → literal lp ⊗ (ClosG ⊗ (literal t ⊗ ⊤Ty)) ⊢ BT (after (just t))
bt-open t m (ms , e , (lc , (rest , tt*))) =
  go (ms fz) (ms (fs fz)) lc e rest
  where
  go : (u v : List Tok) → u Eq.≡ (lp ∷ []) → (u ++ v) Eq.≡ m
     → (ClosG ⊗ (literal t ⊗ ⊤Ty)) v → BT (after (just t)) m
  go .(lp ∷ []) v Eq.refl Eq.refl (ns , f , (cq , (rest2 , tt*))) =
    go2 (ns fz) (ns (fs fz)) f cq rest2
    where
    go2 : (a b : List Tok) → (a ++ b) Eq.≡ v → Closing a × ClosingS a
        → (literal t ⊗ ⊤Ty) b → BT (after (just t)) (lp ∷ v)
    go2 a b Eq.refl ca (os , f2 , (lt , (_ , tt*))) =
      go3 (os fz) (os (fs fz)) lt f2
      where
      go3 : (c d : List Tok) → c Eq.≡ (t ∷ []) → (c ++ d) Eq.≡ b
          → BT (after (just t)) (lp ∷ (a ++ b))
      go3 .(t ∷ []) d Eq.refl Eq.refl = lift (ca .fst (t ∷ d))

bt-wrap : (t : Tok)
  → literal lp ⊗ (TranspG ⊗ (literal rp ⊗ (literal t ⊗ ⊤Ty)))
  ⊢ BT (after (just t))
bt-wrap t m (ms , e , (lc , (rest , tt*))) =
  go (ms fz) (ms (fs fz)) lc e rest
  where
  go : (u v : List Tok) → u Eq.≡ (lp ∷ []) → (u ++ v) Eq.≡ m
     → (TranspG ⊗ (literal rp ⊗ (literal t ⊗ ⊤Ty))) v → BT (after (just t)) m
  go .(lp ∷ []) v Eq.refl Eq.refl (ns , f , (ta , (rest2 , tt*))) =
    go2 (ns fz) (ns (fs fz)) f ta rest2
    where
    go2 : (a b : List Tok) → (a ++ b) Eq.≡ v → Transparent a
        → (literal rp ⊗ (literal t ⊗ ⊤Ty)) b → BT (after (just t)) (lp ∷ v)
    go2 a b Eq.refl ta2 (os , f2 , (lr , (rest3 , tt*))) =
      go3 (os fz) (os (fs fz)) lr f2 rest3
      where
      go3 : (c d : List Tok) → c Eq.≡ (rp ∷ []) → (c ++ d) Eq.≡ b
          → (literal t ⊗ ⊤Ty) d → BT (after (just t)) (lp ∷ (a ++ b))
      go3 .(rp ∷ []) d Eq.refl Eq.refl (ps , f3 , (lt , (_ , tt*))) =
        go4 (ps fz) (ps (fs fz)) lt f3
        where
        go4 : (g h : List Tok) → g Eq.≡ (t ∷ []) → (g ++ h) Eq.≡ d
            → BT (after (just t)) (lp ∷ (a ++ ((rp ∷ []) ++ d)))
        go4 .(t ∷ []) h Eq.refl Eq.refl = lift (cls-open ta2 t h)

bt-vid : literal vid ⊗ ⊤Ty ⊢ BT (headed vid)
bt-vid m (ms , e , (lc , (_ , tt*))) = go (ms fz) (ms (fs fz)) lc e
  where
  go : (u v : List Tok) → u Eq.≡ (vid ∷ []) → (u ++ v) Eq.≡ m
     → BT (headed vid) m
  go .(vid ∷ []) v Eq.refl Eq.refl = lift (cls-vid v)
