{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The bracket-matching cover: a lookahead class that no finite-state
   device gives.

   A word is classified by matching the `(` it opens with, if any, and
   reporting the token that follows the match.  The classes partition every
   word, so they are a `Cover` in the sense `Route` asks for -- and nothing
   about them is a window, an automaton, or a regular language. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Decidable.Bracket where

open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; ++-assoc)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
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

-- The classes.  `after t` is "opens with a `(` whose match is followed by
-- `t`"; `noMatch` is "opens with a `(` that never closes"; `headed c` is
-- "does not open with a `(`"; `blank` is the empty word.

data Cls : Type where
  after   : Maybe Tok → Cls
  noMatch : Cls
  headed  : Tok → Cls
  blank   : Cls

decMTok : (x y : Maybe Tok) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
decMTok nothing nothing = Sum.inl Eq.refl
decMTok nothing (just y) = Sum.inr λ ()
decMTok (just x) nothing = Sum.inr λ ()
decMTok (just x) (just y) = onTokEq (x ≟T y)
  where
  onTokEq : (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
     → (just x Eq.≡ just y) Sum.⊎ ((just x Eq.≡ just y) → Empty.⊥)
  onTokEq (Sum.inl Eq.refl) = Sum.inl Eq.refl
  onTokEq (Sum.inr ne) = Sum.inr λ where Eq.refl → ne Eq.refl

decCls : (x y : Cls) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
decCls (after s) (after t) = onFollowEq (decMTok s t)
  where
  onFollowEq : (s Eq.≡ t) Sum.⊎ ((s Eq.≡ t) → Empty.⊥)
     → (after s Eq.≡ after t) Sum.⊎ ((after s Eq.≡ after t) → Empty.⊥)
  onFollowEq (Sum.inl Eq.refl) = Sum.inl Eq.refl
  onFollowEq (Sum.inr ne) = Sum.inr λ where Eq.refl → ne Eq.refl
decCls (headed c) (headed d) = onHeadEq (c ≟T d)
  where
  onHeadEq : (c Eq.≡ d) Sum.⊎ ((c Eq.≡ d) → Empty.⊥)
     → (headed c Eq.≡ headed d) Sum.⊎ ((headed c Eq.≡ headed d) → Empty.⊥)
  onHeadEq (Sum.inl Eq.refl) = Sum.inl Eq.refl
  onHeadEq (Sum.inr ne) = Sum.inr λ where Eq.refl → ne Eq.refl
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

-- Classifying a word.  This is a metalanguage scan on a model element, so
-- it stays private, exactly as `Lookahead/Window`'s `win` does: it is how
-- the cover is *justified*, and no client may reason with it.

private
  headOf : List Tok → Maybe Tok
  headOf [] = nothing
  headOf (t ∷ _) = just t

  -- Inside the brackets, at depth `d`: report what follows the match.
  -- The token is split before the depth is, so a non-bracket letter
  -- reduces without knowing `d` -- which is what transparency needs.
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

-- Bracket transparency: scanning through a word leaves the depth where it
-- started.  This is the property a grammar owes the cover, and the only
-- thing exported about `chase` -- the scan itself stays private.

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

-- a matched pair around a transparent body, followed by a transparent tail
-- A word that ends by closing one bracket more than it opens.  `Closing`
-- is its effect at depth zero, where the scan stops; `ClosingS` its effect
-- deeper, where the depth merely drops.
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

-- The cover.  The parts are the fibres of `cls`.
--
-- This is a weaker kind of part than `Λ₁`/`Λw`, whose parts are syntactic
-- grammars (`literal c ⊗ ⊤Ty`) with the classifier kept private.  Here
-- there is no such syntactic form short of a balanced-string `μ` plus a
-- match-uniqueness theorem, so the classifier *is* the part.  What is
-- bought: `total` and `disjoint` are one line each.  What is owed: every
-- `into` becomes an induction over a parse tree, which is where the
-- grammar-specific work belongs anyway.

BT : Cls → TheoryTy ℓM tt
BT i m = Lift ℓM (cls m Eq.≡ i)

bracketCover : Cover Cls BT
bracketCover .total m _ = cls m , lift Eq.refl
bracketCover .disjoint i i' ne m (lift p , lift p') =
  Empty.rec (ne (Eq.sym p Eq.∙ p'))

decClsEq : DiscreteEq Cls
decClsEq = decCls

-- The cover's interface, as `⊢`-terms.  Every tensor decomposition in the
-- development happens here, beside the scan it is about; a grammar using
-- this cover composes these and never splits a word itself.

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
  afterLetter (ms fz) (ms (fs fz)) lc e t
  where
  afterLetter : (u v : List Tok) → u Eq.≡ (c ∷ []) → (u ++ v) Eq.≡ m
     → Transparent v → Transparent m
  afterLetter .(c ∷ []) v Eq.refl Eq.refl tv = skipTr c nb tv

cl-rp : literal rp ⊢ ClosG
cl-rp m e =
  Eq.transport (λ z → Closing z × ClosingS z) (Eq.sym e)
    ((λ y → Eq.refl) , (λ d y → Eq.refl))

cl-skip : (c : Tok) → NotBr c → literal c ⊗ ClosG ⊢ ClosG
cl-skip c nb m (ms , e , (lc , (t , tt*))) =
  afterLetter (ms fz) (ms (fs fz)) lc e t
  where
  afterLetter : (u v : List Tok) → u Eq.≡ (c ∷ []) → (u ++ v) Eq.≡ m
     → Closing v × ClosingS v → Closing m × ClosingS m
  afterLetter .(c ∷ []) v Eq.refl Eq.refl cv = skipCl c nb cv

-- a bracket closed by the body itself, then a transparent tail
tr-open : literal lp ⊗ (ClosG ⊗ TranspG) ⊢ TranspG
tr-open m (ms , e , (lc , (rest , tt*))) =
  afterOpen (ms fz) (ms (fs fz)) lc e rest
  where
  afterOpen : (u v : List Tok) → u Eq.≡ (lp ∷ []) → (u ++ v) Eq.≡ m
     → (ClosG ⊗ TranspG) v → Transparent m
  afterOpen .(lp ∷ []) v Eq.refl Eq.refl (ns , f , (cq , (tn , tt*))) =
    afterClosing (ns fz) (ns (fs fz)) f cq tn
    where
    afterClosing : (a b : List Tok) → (a ++ b) Eq.≡ v
        → Closing a × ClosingS a → Transparent b → Transparent (lp ∷ v)
    afterClosing a b Eq.refl ca tb = transp-open (ca .snd) tb

tr-wrap : literal lp ⊗ (TranspG ⊗ (literal rp ⊗ TranspG)) ⊢ TranspG
tr-wrap m (ms , e , (lc , (rest , tt*))) =
  afterOpen (ms fz) (ms (fs fz)) lc e rest
  where
  afterOpen : (u v : List Tok) → u Eq.≡ (lp ∷ []) → (u ++ v) Eq.≡ m
     → (TranspG ⊗ (literal rp ⊗ TranspG)) v → Transparent m
  afterOpen .(lp ∷ []) v Eq.refl Eq.refl (ns , f , (ta , (rest2 , tt*))) =
    afterBody (ns fz) (ns (fs fz)) f ta rest2
    where
    afterBody : (a b : List Tok) → (a ++ b) Eq.≡ v → Transparent a
        → (literal rp ⊗ TranspG) b → Transparent (lp ∷ v)
    afterBody a b Eq.refl ta2 (os , f2 , (lr , (tb , tt*))) =
      afterClose (os fz) (os (fs fz)) lr f2 tb
      where
      afterClose : (c d : List Tok) → c Eq.≡ (rp ∷ []) → (c ++ d) Eq.≡ b
          → Transparent d → Transparent (lp ∷ (a ++ b))
      afterClose .(rp ∷ []) d Eq.refl Eq.refl td = transp-wrap ta2 td

bt-open : (t : Tok)
  → literal lp ⊗ (ClosG ⊗ (literal t ⊗ ⊤Ty)) ⊢ BT (after (just t))
bt-open t m (ms , e , (lc , (rest , tt*))) =
  afterOpen (ms fz) (ms (fs fz)) lc e rest
  where
  afterOpen : (u v : List Tok) → u Eq.≡ (lp ∷ []) → (u ++ v) Eq.≡ m
     → (ClosG ⊗ (literal t ⊗ ⊤Ty)) v → BT (after (just t)) m
  afterOpen .(lp ∷ []) v Eq.refl Eq.refl (ns , f , (cq , (rest2 , tt*))) =
    afterClosing (ns fz) (ns (fs fz)) f cq rest2
    where
    afterClosing : (a b : List Tok) → (a ++ b) Eq.≡ v → Closing a × ClosingS a
        → (literal t ⊗ ⊤Ty) b → BT (after (just t)) (lp ∷ v)
    afterClosing a b Eq.refl ca (os , f2 , (lt , (_ , tt*))) =
      afterFollow (os fz) (os (fs fz)) lt f2
      where
      afterFollow : (c d : List Tok) → c Eq.≡ (t ∷ []) → (c ++ d) Eq.≡ b
          → BT (after (just t)) (lp ∷ (a ++ b))
      afterFollow .(t ∷ []) d Eq.refl Eq.refl = lift (ca .fst (t ∷ d))

bt-wrap : (t : Tok)
  → literal lp ⊗ (TranspG ⊗ (literal rp ⊗ (literal t ⊗ ⊤Ty)))
  ⊢ BT (after (just t))
bt-wrap t m (ms , e , (lc , (rest , tt*))) =
  afterOpen (ms fz) (ms (fs fz)) lc e rest
  where
  afterOpen : (u v : List Tok) → u Eq.≡ (lp ∷ []) → (u ++ v) Eq.≡ m
     → (TranspG ⊗ (literal rp ⊗ (literal t ⊗ ⊤Ty))) v → BT (after (just t)) m
  afterOpen .(lp ∷ []) v Eq.refl Eq.refl (ns , f , (ta , (rest2 , tt*))) =
    afterBody (ns fz) (ns (fs fz)) f ta rest2
    where
    afterBody : (a b : List Tok) → (a ++ b) Eq.≡ v → Transparent a
        → (literal rp ⊗ (literal t ⊗ ⊤Ty)) b → BT (after (just t)) (lp ∷ v)
    afterBody a b Eq.refl ta2 (os , f2 , (lr , (rest3 , tt*))) =
      afterClose (os fz) (os (fs fz)) lr f2 rest3
      where
      afterClose : (c d : List Tok) → c Eq.≡ (rp ∷ []) → (c ++ d) Eq.≡ b
          → (literal t ⊗ ⊤Ty) d → BT (after (just t)) (lp ∷ (a ++ b))
      afterClose .(rp ∷ []) d Eq.refl Eq.refl (ps , f3 , (lt , (_ , tt*))) =
        afterFollow (ps fz) (ps (fs fz)) lt f3
        where
        afterFollow : (g h : List Tok) → g Eq.≡ (t ∷ []) → (g ++ h) Eq.≡ d
            → BT (after (just t)) (lp ∷ (a ++ ((rp ∷ []) ++ d)))
        afterFollow .(t ∷ []) h Eq.refl Eq.refl = lift (cls-open ta2 t h)

bt-vid : literal vid ⊗ ⊤Ty ⊢ BT (headed vid)
bt-vid m (ms , e , (lc , (_ , tt*))) = afterLetter (ms fz) (ms (fs fz)) lc e
  where
  afterLetter : (u v : List Tok) → u Eq.≡ (vid ∷ []) → (u ++ v) Eq.≡ m
     → BT (headed vid) m
  afterLetter .(vid ∷ []) v Eq.refl Eq.refl = lift (cls-vid v)
