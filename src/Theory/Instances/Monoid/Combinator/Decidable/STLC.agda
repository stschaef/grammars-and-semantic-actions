{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A simply typed lambda calculus with data: three mutually recursive
   nonterminals, twenty-six productions, parsed predictively.

     A ::= bool | nat | arr A A | prod A A | list A
     v ::= f | g | n | x | xs
     t ::= true | false | if t then t else t
         | zero | suc t | natrec t t t
         | lam v : A . t | app t t
         | pair t t | fst t | snd t
         | nil : A | cons t t | foldr t t t
         | let v = t in t | v

   Every former is prefix or keyword-led, so every production is terminal-led
   and the table's type is the whole LL(1) argument.  `Src` below builds the
   token list a program is, so the tests read as programs. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Combinator.Decidable.STLC where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; length)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Properties using (discreteℕ)
open import Cubical.Relation.Nullary.Base using (Discrete)
open import Cubical.Relation.Nullary.Properties using (sectionDiscrete)
open import Cubical.Relation.Nullary.DiscreteEq using (DiscreteEq ; Discrete→DiscreteEq)
open import Cubical.Data.Unit using (tt)

data Tok : Type ℓ-zero where
  kbool knat karr kprod klist ktrue kfalse kif kthen kelse kzero ksuc knatrec klam kcolon kdot kapp kpair kfst ksnd knil kcons kfoldr klet kassign kin vf vg vn vx vxs : Tok

-- Deciding equality of 31 nullary constructors.  This used to be a
-- 961-line 31x31 table -- 48% of this file, and ~2.4% of the whole
-- branch.  Numbering the tokens and transporting `discreteℕ` along the
-- section costs two 31-clause functions instead, and every clause is
-- forced by the constructor it names rather than by the 30 it does not.
--
-- `uncode` reads the table back through a list rather than by matching
-- numerals, because Agda expands a literal pattern to that many `suc`s
-- and refuses past 20.  Going through `toks` keeps each
-- `uncode (code t) ≡ t` true by computation, so the section is 31
-- `refl`s.
toks : List Tok
toks =
    kbool
  ∷ knat
  ∷ karr
  ∷ kprod
  ∷ klist
  ∷ ktrue
  ∷ kfalse
  ∷ kif
  ∷ kthen
  ∷ kelse
  ∷ kzero
  ∷ ksuc
  ∷ knatrec
  ∷ klam
  ∷ kcolon
  ∷ kdot
  ∷ kapp
  ∷ kpair
  ∷ kfst
  ∷ ksnd
  ∷ knil
  ∷ kcons
  ∷ kfoldr
  ∷ klet
  ∷ kassign
  ∷ kin
  ∷ vf
  ∷ vg
  ∷ vn
  ∷ vx
  ∷ vxs
  ∷ []

code : Tok → ℕ
code kbool = 0
code knat = 1
code karr = 2
code kprod = 3
code klist = 4
code ktrue = 5
code kfalse = 6
code kif = 7
code kthen = 8
code kelse = 9
code kzero = 10
code ksuc = 11
code knatrec = 12
code klam = 13
code kcolon = 14
code kdot = 15
code kapp = 16
code kpair = 17
code kfst = 18
code ksnd = 19
code knil = 20
code kcons = 21
code kfoldr = 22
code klet = 23
code kassign = 24
code kin = 25
code vf = 26
code vg = 27
code vn = 28
code vx = 29
code vxs = 30

uncode : ℕ → Tok
uncode n = go n toks
  where
  go : ℕ → List Tok → Tok
  go _       []       = kbool
  go zero    (t ∷ _)  = t
  go (suc k) (_ ∷ ts) = go k ts

uncode-code : (t : Tok) → uncode (code t) ≡ t
uncode-code kbool = refl
uncode-code knat = refl
uncode-code karr = refl
uncode-code kprod = refl
uncode-code klist = refl
uncode-code ktrue = refl
uncode-code kfalse = refl
uncode-code kif = refl
uncode-code kthen = refl
uncode-code kelse = refl
uncode-code kzero = refl
uncode-code ksuc = refl
uncode-code knatrec = refl
uncode-code klam = refl
uncode-code kcolon = refl
uncode-code kdot = refl
uncode-code kapp = refl
uncode-code kpair = refl
uncode-code kfst = refl
uncode-code ksnd = refl
uncode-code knil = refl
uncode-code kcons = refl
uncode-code kfoldr = refl
uncode-code klet = refl
uncode-code kassign = refl
uncode-code kin = refl
uncode-code vf = refl
uncode-code vg = refl
uncode-code vn = refl
uncode-code vx = refl
uncode-code vxs = refl

discreteTok : Discrete Tok
discreteTok = sectionDiscrete uncode code uncode-code discreteℕ

_≟T_ : DiscreteEq Tok
_≟T_ = Discrete→DiscreteEq discreteTok

open import Theory.Instances.Monoid.Combinator.Decidable.Synthesis Tok _≟T_

-- the three nonterminals
data NT : Type ℓ-zero where
  Ty Tm Var : NT

-- The grammar, as rules.  Every production is led by its keyword, so the
-- classes with no production need not be mentioned at all -- the `_ = none`
-- catch-alls below were the table saying nothing, three times over.
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

-- twenty-five productions across three nonterminals, and no two of them
-- share a leading keyword -- computed, not asserted
stlcLL1 : SS.clashes Eq.≡ []
stlcLL1 = Eq.refl

stlc : Table NT
stlc = SS.table

open Gen stlc

Type′ Term Name : TheoryTy ℓG tt
Type′ = S Ty
Term = S Tm
Name = S Var

parseTy : Decidable Type′
parseTy = decide Ty

parseTm : Decidable Term
parseTm = decide Tm

-- Raw syntax: a program is the token list these build.

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

-- numerals, so the programs can mention numbers
`num : ℕ → Src
`num zero = `zero
`num (suc m) = `suc (`num m)

-- Parsing.  Every `Eq.refl` is the parser running on the token list.

-- types
yes-nat : Type′ `nat
yes-nat = theYes (parseTy `nat tt) Eq.refl

yes-arr : Type′ (`nat `⇒ `bool)
yes-arr = theYes (parseTy (`nat `⇒ `bool) tt) Eq.refl

yes-listprod : Type′ (`list (`nat `× (`nat `⇒ `bool)))
yes-listprod = theYes (parseTy (`list (`nat `× (`nat `⇒ `bool))) tt) Eq.refl

-- terms
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

-- Two real programs.

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

-- how big those really are, as token lists
fib-size : length fibSrc ≡ 65
fib-size = refl

sum-size : length sumSrc ≡ 47
sum-size = refl

-- ...and the rejections, which are refutations.

-- the two languages do not accept each other
no-type-as-term : ¬Ty Term `nat
no-type-as-term = theNo (parseTm `nat tt) Eq.refl

no-term-as-type : ¬Ty Type′ (`var vx)
no-term-as-type = theNo (parseTy (`var vx) tt) Eq.refl

-- a binder with no annotation
no-bare-lam : ¬Ty Term (klam ∷ vx ∷ kdot ∷ vx ∷ [])
no-bare-lam = theNo (parseTm (klam ∷ vx ∷ kdot ∷ vx ∷ []) tt) Eq.refl

-- an `if` with no `else` branch
no-half-if : ¬Ty Term (kif ∷ ktrue ∷ kthen ∷ kzero ∷ [])
no-half-if = theNo (parseTm (kif ∷ ktrue ∷ kthen ∷ kzero ∷ []) tt) Eq.refl

-- a recursor short one argument
no-short-natrec : ¬Ty Term (knatrec ∷ kzero ∷ kzero ∷ [])
no-short-natrec = theNo (parseTm (knatrec ∷ kzero ∷ kzero ∷ []) tt) Eq.refl

-- a keyword in a type position
no-kw-type : ¬Ty Type′ (karr ∷ knat ∷ ktrue ∷ [])
no-kw-type = theNo (parseTy (karr ∷ knat ∷ ktrue ∷ []) tt) Eq.refl

-- and a whole program with one token too many
no-trailing : ¬Ty Term (sumSrc ++ (kzero ∷ []))
no-trailing = theNo (parseTm (sumSrc ++ (kzero ∷ [])) tt) Eq.refl

-- The parse tree, as data.

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

-- Pass 1: the concrete tree becomes an abstract one.

import Cubical.Data.Maybe as M

private
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

-- Pass 2: scope checking.  Names become de Bruijn indices, and an unbound
-- name is `nothing`.

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

-- Pass 3: type inference.  Every binder is annotated, so nothing is
-- checked against an expected type -- inference alone suffices.

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

-- The whole front end: token list → parse tree → AST → scoped → typed.

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

-- ...run on the two programs.

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

-- ...and each pass rejects what is its business to reject.

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

-- ...and a few more type errors
badSuc : tyOf (`suc `true) ≡ M.nothing
badSuc = refl

badApp : tyOf (idSrc `$ `true) ≡ M.nothing
badApp = refl

badCons : tyOf (`cons `true (`nil `nat)) ≡ M.nothing
badCons = refl

badFold : tyOf (`foldr idSrc `zero (`cons (`num 1) (`nil `nat))) ≡ M.nothing
badFold = refl

-- Pass 2, completed.  A `Maybe` says nothing when it says nothing, so the
-- pass is made to answer with a decision: a derivation, or a refutation of
-- every derivation.  The refutations come from inversion -- one line per
-- former, since `Scoped` is an inductive family.

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

-- ...and the decision, one clause per former
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

-- Pass 3, completed.  Same move: `Typed` is an inductive family, and the
-- decision answers with a derivation or a refutation of all of them.  What
-- makes the refutations available is that this calculus is fully annotated,
-- hence *uniquely* typed: a mismatch with the inferred type really does
-- refute, by `unique`.

open import Cubical.Data.Sigma using (Σ-syntax ; _×_)

_≟ty_ : (A B : ATy) → (A Eq.≡ B) Sum.⊎ ((A Eq.≡ B) → Empty.⊥)
Bo ≟ty Bo = Sum.inl Eq.refl
Na ≟ty Na = Sum.inl Eq.refl
Ar a b ≟ty Ar a' b' = go (a ≟ty a') (b ≟ty b')
  where
  go : (a Eq.≡ a') Sum.⊎ ((a Eq.≡ a') → Empty.⊥)
     → (b Eq.≡ b') Sum.⊎ ((b Eq.≡ b') → Empty.⊥)
     → (Ar a b Eq.≡ Ar a' b') Sum.⊎ ((Ar a b Eq.≡ Ar a' b') → Empty.⊥)
  go (Sum.inl Eq.refl) (Sum.inl Eq.refl) = Sum.inl Eq.refl
  go (Sum.inr ne) _ = Sum.inr λ where Eq.refl → ne Eq.refl
  go _ (Sum.inr ne) = Sum.inr λ where Eq.refl → ne Eq.refl
Pr a b ≟ty Pr a' b' = go (a ≟ty a') (b ≟ty b')
  where
  go : (a Eq.≡ a') Sum.⊎ ((a Eq.≡ a') → Empty.⊥)
     → (b Eq.≡ b') Sum.⊎ ((b Eq.≡ b') → Empty.⊥)
     → (Pr a b Eq.≡ Pr a' b') Sum.⊎ ((Pr a b Eq.≡ Pr a' b') → Empty.⊥)
  go (Sum.inl Eq.refl) (Sum.inl Eq.refl) = Sum.inl Eq.refl
  go (Sum.inr ne) _ = Sum.inr λ where Eq.refl → ne Eq.refl
  go _ (Sum.inr ne) = Sum.inr λ where Eq.refl → ne Eq.refl
Li a ≟ty Li a' = go (a ≟ty a')
  where
  go : (a Eq.≡ a') Sum.⊎ ((a Eq.≡ a') → Empty.⊥)
     → (Li a Eq.≡ Li a') Sum.⊎ ((Li a Eq.≡ Li a') → Empty.⊥)
  go (Sum.inl Eq.refl) = Sum.inl Eq.refl
  go (Sum.inr ne) = Sum.inr λ where Eq.refl → ne Eq.refl
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

-- a context lookup, as a function: shadowing is then automatic and the
-- lookup is deterministic by construction
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

-- the context is deterministic...
justInj : {A B : ATy} → M.just A Eq.≡ M.just B → A Eq.≡ B
justInj Eq.refl = Eq.refl

uniqueᶜ : {x : Tok} {A B : ATy} {Γ : Ctx}
  → lookupC Γ x Eq.≡ M.just A → lookupC Γ x Eq.≡ M.just B → A Eq.≡ B
uniqueᶜ p q = justInj (Eq.sym p Eq.∙ q)

-- ...and so, every binder being annotated, is the typing
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

-- views, so a former that needs a shaped type says so once
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

-- Running the two complete passes.  `theD` extracts a derivation and
-- `theNotD` a refutation, exactly as `theYes`/`theNo` do for the parser.

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

-- scope checking: a derivation, and for a free variable a refutation
fib-scoped : Scoped [] fibAST
fib-scoped = theD (scoped? [] fibAST) Eq.refl

sum-scoped : Scoped [] sumAST
sum-scoped = theD (scoped? [] sumAST) Eq.refl

unbound-refuted : Scoped [] (Nm vx) → Empty.⊥
unbound-refuted = theNotD (scoped? [] (Nm vx)) Eq.refl

-- ...but bound under a binder that binds it
bound-scoped : Scoped [] (Lam vx Na (Nm vx))
bound-scoped = theD (scoped? [] (Lam vx Na (Nm vx))) Eq.refl

-- type checking: a derivation carrying its type
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

-- ...and refutations of *every* derivation, which is what completeness buys
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
