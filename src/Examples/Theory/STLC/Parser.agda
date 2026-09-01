{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- STLC with data, parsed predictively; every production is terminal-led.

     A ::= bool | nat | arr A A | prod A A | list A
     v ::= f | g | n | x | xs
     t ::= true | false | if t then t else t
         | zero | suc t | natrec t t t
         | lam v : A . t | app t t
         | pair t t | fst t | snd t
         | nil : A | cons t t | foldr t t t
         | let v = t in t | v
-}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Examples.Theory.STLC.Parser where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; length)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Unit using (tt)

open import Examples.Theory.STLC.Tokens public

open import Theory.Instances.Monoid.Combinator.Decidable.Synthesis Tok _≟T_
  public

data NT : Type ℓ-zero where
  Ty Tm Var : NT

stlcRules : Rules NT
stlcRules .Rules.nullable _ = false

-- A ::= bool | nat | arr A A | prod A A | list A
stlcRules .Rules.of Ty =
    (kbool  , [])
  ∷ (knat   , [])
  ∷ (karr   , nt Ty ∷ nt Ty ∷ [])
  ∷ (kprod  , nt Ty ∷ nt Ty ∷ [])
  ∷ (klist  , nt Ty ∷ [])
  ∷ []

stlcRules .Rules.of Var =
    (vf , []) ∷ (vg , []) ∷ (vn , []) ∷ (vx , []) ∷ (vxs , []) ∷ []

stlcRules .Rules.of Tm =
    (ktrue   , [])
  ∷ (kfalse  , [])
  ∷ (kif     , nt Tm ∷ tm kthen ∷ nt Tm ∷ tm kelse ∷ nt Tm ∷ [])
  ∷ (kzero   , [])
  ∷ (ksuc    , nt Tm ∷ [])
  ∷ (knatrec , nt Tm ∷ nt Tm ∷ nt Tm ∷ [])
  ∷ (klam    , nt Var ∷ tm kcolon ∷ nt Ty ∷ tm kdot ∷ nt Tm ∷ [])
  ∷ (kapp    , nt Tm ∷ nt Tm ∷ [])
  ∷ (kpair   , nt Tm ∷ nt Tm ∷ [])
  ∷ (kfst    , nt Tm ∷ [])
  ∷ (ksnd    , nt Tm ∷ [])
  ∷ (knil    , tm kcolon ∷ nt Ty ∷ [])
  ∷ (kcons   , nt Tm ∷ nt Tm ∷ [])
  ∷ (kfoldr  , nt Tm ∷ nt Tm ∷ nt Tm ∷ [])
  ∷ (klet    , nt Var ∷ tm kassign ∷ nt Tm ∷ tm kin ∷ nt Tm ∷ [])
  ∷ (vf , []) ∷ (vg , []) ∷ (vn , []) ∷ (vx , []) ∷ (vxs , [])
  ∷ []

module SS = Synth (Ty ∷ Tm ∷ Var ∷ []) stlcRules

-- no two productions share a leading keyword -- computed, not asserted
stlcLL1 : SS.clashes Eq.≡ []
stlcLL1 = Eq.refl

stlc : Table NT
stlc = SS.table

open Gen stlc public

Type′ Term Name : TheoryTy ℓG tt
Type′ = S Ty
Term = S Tm
Name = S Var

parseTy : Decidable Type′
parseTy = decide Ty

parseTm : Decidable Term
parseTm = decide Tm

Src : Type ℓ-zero
Src = List Tok

infixl 8 _`$_
infixr 2 `λ_∶_∙_
infixr 2 `let_≔_`in_
infixr 3 `if_`then_`else_

`bool `nat : Src
`bool = kbool ∷ []
`nat = knat ∷ []

_`⇒_ _`×_ : Src → Src → Src
A `⇒ B = karr ∷ A ++ B
A `× B = kprod ∷ A ++ B

`list : Src → Src
`list A = klist ∷ A

`true `false `zero : Src
`true = ktrue ∷ []
`false = kfalse ∷ []
`zero = kzero ∷ []

`suc `fst `snd : Src → Src
`suc t = ksuc ∷ t
`fst t = kfst ∷ t
`snd t = ksnd ∷ t

`var : Tok → Src
`var x = x ∷ []

`if_`then_`else_ : Src → Src → Src → Src
`if c `then a `else b = kif ∷ c ++ kthen ∷ a ++ kelse ∷ b

`natrec : Src → Src → Src → Src
`natrec z s n = knatrec ∷ z ++ s ++ n

`λ_∶_∙_ : Tok → Src → Src → Src
`λ x ∶ A ∙ t = klam ∷ x ∷ kcolon ∷ A ++ kdot ∷ t

_`$_ : Src → Src → Src
t `$ u = kapp ∷ t ++ u

`pair : Src → Src → Src
`pair a b = kpair ∷ a ++ b

`nil : Src → Src
`nil A = knil ∷ kcolon ∷ A

`cons : Src → Src → Src
`cons h t = kcons ∷ h ++ t

`foldr : Src → Src → Src → Src
`foldr f z xs = kfoldr ∷ f ++ z ++ xs

`let_≔_`in_ : Tok → Src → Src → Src
`let x ≔ t `in u = klet ∷ x ∷ kassign ∷ t ++ kin ∷ u

`num : ℕ → Src
`num zero = `zero
`num (suc m) = `suc (`num m)

yes-nat : Type′ `nat
yes-nat = theYes (parseTy `nat tt) Eq.refl

yes-arr : Type′ (`nat `⇒ `bool)
yes-arr = theYes (parseTy (`nat `⇒ `bool) tt) Eq.refl

yes-listprod : Type′ (`list (`nat `× (`nat `⇒ `bool)))
yes-listprod = theYes (parseTy (`list (`nat `× (`nat `⇒ `bool))) tt) Eq.refl

idSrc : Src
idSrc = `λ vx ∶ `nat ∙ `var vx

yes-id : Term idSrc
yes-id = theYes (parseTm idSrc tt) Eq.refl

yes-ite : Term (`if `true `then `zero `else (`suc `zero))
yes-ite = theYes (parseTm (`if `true `then `zero `else (`suc `zero)) tt) Eq.refl

yes-proj : Term (`fst (`pair `zero `true))
yes-proj = theYes (parseTm (`fst (`pair `zero `true)) tt) Eq.refl

yes-list : Term (`cons (`num 1) (`cons (`num 2) (`nil `nat)))
yes-list = theYes (parseTm (`cons (`num 1) (`cons (`num 2) (`nil `nat))) tt) Eq.refl

-- addition, by the recursor:  λ n : nat . λ x : nat . natrec x (λ g : nat . suc g) n
addSrc : Src
addSrc = `λ vn ∶ `nat ∙ `λ vx ∶ `nat ∙
           `natrec (`var vx) (`λ vg ∶ `nat ∙ `suc (`var vg)) (`var vn)

yes-add : Term addSrc
yes-add = theYes (parseTm addSrc tt) Eq.refl

-- fib, by the pair trick:
--   let g = add in
--   let f = λ n : nat . fst (natrec ⟨0,1⟩ (λ x : nat × nat . ⟨snd x, g (fst x) (snd x)⟩) n)
--   in f 5
fibSrc : Src
fibSrc =
  `let vg ≔ addSrc `in
  `let vf ≔ (`λ vn ∶ `nat ∙
               `fst (`natrec (`pair `zero (`suc `zero))
                             (`λ vx ∶ (`nat `× `nat) ∙
                                `pair (`snd (`var vx))
                                      (`var vg `$ `fst (`var vx) `$ `snd (`var vx)))
                             (`var vn)))
  `in (`var vf `$ `num 5)

yes-fib : Term fibSrc
yes-fib = theYes (parseTm fibSrc tt) Eq.refl

-- summing a list with the fold former:
--   let f = add in let xs = 1 ∷ 2 ∷ 3 ∷ nil : nat in foldr f 0 xs
sumSrc : Src
sumSrc =
  `let vf ≔ addSrc `in
  `let vxs ≔ `cons (`num 1) (`cons (`num 2) (`cons (`num 3) (`nil `nat))) `in
  `foldr (`var vf) `zero (`var vxs)

yes-sum : Term sumSrc
yes-sum = theYes (parseTm sumSrc tt) Eq.refl

fib-size : length fibSrc ≡ 65
fib-size = refl

sum-size : length sumSrc ≡ 47
sum-size = refl

no-type-as-term : ¬Ty Term `nat
no-type-as-term = theNo (parseTm `nat tt) Eq.refl

no-term-as-type : ¬Ty Type′ (`var vx)
no-term-as-type = theNo (parseTy (`var vx) tt) Eq.refl

no-bare-lam : ¬Ty Term (klam ∷ vx ∷ kdot ∷ vx ∷ [])
no-bare-lam = theNo (parseTm (klam ∷ vx ∷ kdot ∷ vx ∷ []) tt) Eq.refl

no-half-if : ¬Ty Term (kif ∷ ktrue ∷ kthen ∷ kzero ∷ [])
no-half-if = theNo (parseTm (kif ∷ ktrue ∷ kthen ∷ kzero ∷ []) tt) Eq.refl

no-short-natrec : ¬Ty Term (knatrec ∷ kzero ∷ kzero ∷ [])
no-short-natrec = theNo (parseTm (knatrec ∷ kzero ∷ kzero ∷ []) tt) Eq.refl

no-kw-type : ¬Ty Type′ (karr ∷ knat ∷ ktrue ∷ [])
no-kw-type = theNo (parseTy (karr ∷ knat ∷ ktrue ∷ []) tt) Eq.refl

no-trailing : ¬Ty Term (sumSrc ++ (kzero ∷ []))
no-trailing = theNo (parseTm (sumSrc ++ (kzero ∷ [])) tt) Eq.refl

open import Cubical.Data.Nat using (_+_)

nodes : Tree → ℕ
nodes (node _ ts) = suc (go ts)
  where
  go : List Tree → ℕ
  go [] = 0
  go (t ∷ ts) = nodes t + go ts
nodes eps = 1

fibTree sumTree : Tree
fibTree = toTree Tm fibSrc yes-fib
sumTree = toTree Tm sumSrc yes-sum

fib-nodes : nodes fibTree ≡ 51
fib-nodes = refl

sum-nodes : nodes sumTree ≡ 36
sum-nodes = refl

