{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The STLC front end, run on token lists.

   These are the *component* suites: the parser alone, then the three
   elaboration passes composed, then the two completed passes with their
   refutations.  Inputs here are token lists built by the `Src` notation,
   which is as close to source text as this alphabet gets.  For the same
   language read from actual text, see `Pipeline/STLCTests`. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Combinator.Decidable.STLCTests where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; length)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Sigma using (fst)
open import Cubical.Data.Unit using (tt)
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no)
import Cubical.Data.Maybe as M

open import Theory.Instances.Monoid.Combinator.Decidable.STLC

-- Parsing.  Every `Eq.refl` is the parser running on the token list.

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

fib-size : length fibSrc ≡ 65
fib-size = refl

sum-size : length sumSrc ≡ 47
sum-size = refl

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

nodes : Tree → ℕ
nodes (node _ ts) = suc (sumNodes ts)
  where
  sumNodes : List Tree → ℕ
  sumNodes [] = 0
  sumNodes (t ∷ ts) = nodes t + sumNodes ts
nodes eps = 1

fibTree sumTree : Tree
fibTree = toTree Tm fibSrc yes-fib
sumTree = toTree Tm sumSrc yes-sum

fib-nodes : nodes fibTree ≡ 51
fib-nodes = refl

sum-nodes : nodes sumTree ≡ 36
sum-nodes = refl

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

-- Pass 2, completed.  A `Maybe` says nothing when it says nothing, so the

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
