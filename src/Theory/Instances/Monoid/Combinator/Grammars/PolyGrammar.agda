{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Parenthesised multivariate polynomials, as a grammar for the combinator
   library.  Variables come from any discrete `V`; a variable, a numeral
   and an exponent are each one token, so nothing here lexes.

     E ::= ( E ) K | v K | n Q | - E
     Q ::= / m K | + E | * E | ^ n K | ε
     K ::=         + E | * E | ^ n K | ε

   Two constraints fix that shape.  Every production begins with a
   terminal, because `call` answers only at proper suffixes -- so the
   usual `E ::= T E'` factoring is inlined, and precedence is what the
   parentheses are for.  And the grammar is left-factored, so one token
   decides every production: `QTag` is `ℕ ⊎ KTag`, and FIRST(Q) is
   disjoint from FOLLOW(Q), which decides the ε-production too.

   The grammar is `μ polyCode`; the tag decidability that `Choice` asks
   for is derived below. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open import Cubical.Data.Sum as Sum using (_⊎_)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Grammars.PolyGrammar
  (V : Type ℓ-zero)
  (_≟V_ : (a b : V) → (a Eq.≡ b) Sum.⊎ ((a Eq.≡ b) → Empty.⊥))
  where

open import Cubical.Data.Sum.Properties using (isSet⊎)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Unit using (Unit ; tt ; tt* ; isSetUnit)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Properties using (isSetℕ ; discreteℕ)
open import Cubical.Relation.Nullary.Base using (Discrete ; decRec ; yes ; no)
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)

-- The alphabet.  Brackets, the three operators, the fraction bar, and the
-- two families of literals.

data Tok : Type ℓ-zero where
  lp rp : Tok
  plus  : Tok
  times : Tok
  slash : Tok
  minus : Tok
  caret : Tok
  var   : V → Tok
  nat   : ℕ → Tok

private
  -- Decidable equality on `ℕ`, in the form the combinators ask for -- and
  -- by structural recursion, not via `discreteℕ`.  Going through
  -- `Eq.pathToEq` produces a proof that is *not* `Eq.refl`, so `dec-lit⊗-at`
  -- gets stuck on it and a matched numeral never computes.
  _≟ℕ_ : (a b : ℕ) → (a Eq.≡ b) Sum.⊎ ((a Eq.≡ b) → Empty.⊥)
  zero ≟ℕ zero = Sum.inl Eq.refl
  zero ≟ℕ suc b = Sum.inr λ ()
  suc a ≟ℕ zero = Sum.inr λ ()
  suc a ≟ℕ suc b = onPredEq (a ≟ℕ b)
    where
    onPredEq : (a Eq.≡ b) Sum.⊎ ((a Eq.≡ b) → Empty.⊥)
       → (suc a Eq.≡ suc b) Sum.⊎ ((suc a Eq.≡ suc b) → Empty.⊥)
    onPredEq (Sum.inl Eq.refl) = Sum.inl Eq.refl
    onPredEq (Sum.inr ne) = Sum.inr λ where Eq.refl → ne Eq.refl

-- The decision the combinators ask for.  It is `Eq.≡` rather than a path:
-- `Sum.inl Eq.refl` is what makes a matched letter *compute*.
_≟_ : (a b : Tok) → (a Eq.≡ b) Sum.⊎ ((a Eq.≡ b) → Empty.⊥)
lp ≟ lp = Sum.inl Eq.refl
rp ≟ rp = Sum.inl Eq.refl
plus ≟ plus = Sum.inl Eq.refl
times ≟ times = Sum.inl Eq.refl
slash ≟ slash = Sum.inl Eq.refl
minus ≟ minus = Sum.inl Eq.refl
caret ≟ caret = Sum.inl Eq.refl
var v ≟ var w = onVarEq (v ≟V w)
  where
  onVarEq : (v Eq.≡ w) Sum.⊎ ((v Eq.≡ w) → Empty.⊥)
     → (var v Eq.≡ var w) Sum.⊎ ((var v Eq.≡ var w) → Empty.⊥)
  onVarEq (Sum.inl Eq.refl) = Sum.inl Eq.refl
  onVarEq (Sum.inr ne) = Sum.inr λ where Eq.refl → ne Eq.refl
nat n ≟ nat n' = onIndexEq (n ≟ℕ n')
  where
  onIndexEq : (n Eq.≡ n') Sum.⊎ ((n Eq.≡ n') → Empty.⊥)
     → (nat n Eq.≡ nat n') Sum.⊎ ((nat n Eq.≡ nat n') → Empty.⊥)
  onIndexEq (Sum.inl Eq.refl) = Sum.inl Eq.refl
  onIndexEq (Sum.inr ne) = Sum.inr λ where Eq.refl → ne Eq.refl
lp ≟ rp = Sum.inr λ ()
lp ≟ plus = Sum.inr λ ()
lp ≟ times = Sum.inr λ ()
lp ≟ slash = Sum.inr λ ()
lp ≟ minus = Sum.inr λ ()
lp ≟ caret = Sum.inr λ ()
lp ≟ var _ = Sum.inr λ ()
lp ≟ nat _ = Sum.inr λ ()
rp ≟ lp = Sum.inr λ ()
rp ≟ plus = Sum.inr λ ()
rp ≟ times = Sum.inr λ ()
rp ≟ slash = Sum.inr λ ()
rp ≟ minus = Sum.inr λ ()
rp ≟ caret = Sum.inr λ ()
rp ≟ var _ = Sum.inr λ ()
rp ≟ nat _ = Sum.inr λ ()
plus ≟ lp = Sum.inr λ ()
plus ≟ rp = Sum.inr λ ()
plus ≟ times = Sum.inr λ ()
plus ≟ slash = Sum.inr λ ()
plus ≟ minus = Sum.inr λ ()
plus ≟ caret = Sum.inr λ ()
plus ≟ var _ = Sum.inr λ ()
plus ≟ nat _ = Sum.inr λ ()
times ≟ lp = Sum.inr λ ()
times ≟ rp = Sum.inr λ ()
times ≟ plus = Sum.inr λ ()
times ≟ slash = Sum.inr λ ()
times ≟ minus = Sum.inr λ ()
times ≟ caret = Sum.inr λ ()
times ≟ var _ = Sum.inr λ ()
times ≟ nat _ = Sum.inr λ ()
slash ≟ lp = Sum.inr λ ()
slash ≟ rp = Sum.inr λ ()
slash ≟ plus = Sum.inr λ ()
slash ≟ times = Sum.inr λ ()
slash ≟ minus = Sum.inr λ ()
slash ≟ caret = Sum.inr λ ()
slash ≟ var _ = Sum.inr λ ()
slash ≟ nat _ = Sum.inr λ ()
minus ≟ lp = Sum.inr λ ()
minus ≟ rp = Sum.inr λ ()
minus ≟ plus = Sum.inr λ ()
minus ≟ times = Sum.inr λ ()
minus ≟ slash = Sum.inr λ ()
minus ≟ caret = Sum.inr λ ()
minus ≟ var _ = Sum.inr λ ()
minus ≟ nat _ = Sum.inr λ ()
caret ≟ lp = Sum.inr λ ()
caret ≟ rp = Sum.inr λ ()
caret ≟ plus = Sum.inr λ ()
caret ≟ times = Sum.inr λ ()
caret ≟ slash = Sum.inr λ ()
caret ≟ minus = Sum.inr λ ()
caret ≟ var _ = Sum.inr λ ()
caret ≟ nat _ = Sum.inr λ ()
var _ ≟ lp = Sum.inr λ ()
var _ ≟ rp = Sum.inr λ ()
var _ ≟ plus = Sum.inr λ ()
var _ ≟ times = Sum.inr λ ()
var _ ≟ slash = Sum.inr λ ()
var _ ≟ minus = Sum.inr λ ()
var _ ≟ caret = Sum.inr λ ()
var _ ≟ nat _ = Sum.inr λ ()
nat _ ≟ lp = Sum.inr λ ()
nat _ ≟ rp = Sum.inr λ ()
nat _ ≟ plus = Sum.inr λ ()
nat _ ≟ times = Sum.inr λ ()
nat _ ≟ slash = Sum.inr λ ()
nat _ ≟ minus = Sum.inr λ ()
nat _ ≟ caret = Sum.inr λ ()
nat _ ≟ var _ = Sum.inr λ ()

open import Theory.Instances.Monoid.Combinator.Core Tok _≟_ public
  hiding (Maybe ; just ; nothing)
open import Theory.Instances.Monoid.Residual Tok isSetAlphabet
  using (⟦⊗e⟧ ; ⟦⊗e⟧⁻ ; ⊗⊕ᴰ-distL ; ⊗⊕ᴰ-distR)

ℓG : Level
ℓG = ℓ-max ℓM (ℓ-suc ℓ-zero)

-- The nonterminals and their production tags.  A tag is a *sum*, not a
-- `data`, so that `isSet` -- all a code asks of it -- is compositional;
-- the pattern synonyms are what the productions are then written with.

data Nt : Type ℓ-zero where
  expr rest numTail : Nt

-- E ::= ( E ) K | v K | n Q | - E
ETag : Type ℓ-zero
ETag = Unit ⊎ (V ⊎ (ℕ ⊎ Unit))

pattern paren  = Sum.inl tt
pattern atom v = Sum.inr (Sum.inl v)
pattern num n  = Sum.inr (Sum.inr (Sum.inl n))
pattern neg    = Sum.inr (Sum.inr (Sum.inr tt))

-- K ::= + E | * E | ^ n K | ε
KTag : Type ℓ-zero
KTag = Unit ⊎ (Unit ⊎ (ℕ ⊎ Unit))

pattern add   = Sum.inl tt
pattern mul   = Sum.inr (Sum.inl tt)
pattern pow n = Sum.inr (Sum.inr (Sum.inl n))
pattern stop  = Sum.inr (Sum.inr (Sum.inr tt))

-- Q ::= / m K | K.  The left-factoring is the whole content of this type:
-- after a numeral comes a denominator, or anything a `K` admits.
QTag : Type ℓ-zero
QTag = ℕ ⊎ KTag

pattern den m  = Sum.inl m
pattern more t = Sum.inr t

discreteV : Discrete V
discreteV a b = Sum.rec (λ p → yes (Eq.eqToPath p))
                        (λ ne → no λ p → ne (Eq.pathToEq p)) (a ≟V b)

isSetETag : isSet ETag
isSetETag =
  isSet⊎ isSetUnit
    (isSet⊎ (Discrete→isSet discreteV) (isSet⊎ isSetℕ isSetUnit))

isSetKTag : isSet KTag
isSetKTag =
  isSet⊎ isSetUnit (isSet⊎ isSetUnit (isSet⊎ isSetℕ isSetUnit))

isSetQTag : isSet QTag
isSetQTag = isSet⊎ isSetℕ isSetKTag

-- The functor.  A body is the right-nested tensor of its symbols; `μ` of
-- this is the grammar.

private
  Code : Type _
  Code = Functor ℓM Nt (λ _ → tt) tt

  infixr 5 _⊗ᶜ_
  _⊗ᶜ_ : Code → Code → Code
  F ⊗ᶜ G = ⊗e _⊙_ (two F G)

  letter : Tok → Code
  letter c = k (literal c)

  nonterm : Nt → Code
  nonterm n = Var n

  eps : Code
  eps = k εTy

  exprBranch : ETag → Code
  exprBranch paren = letter lp ⊗ᶜ nonterm expr ⊗ᶜ letter rp ⊗ᶜ nonterm rest
  exprBranch (atom v) = letter (var v) ⊗ᶜ nonterm rest
  exprBranch (num n) = letter (nat n) ⊗ᶜ nonterm numTail
  exprBranch neg = letter minus ⊗ᶜ nonterm expr

  restBranch : KTag → Code
  restBranch add = letter plus ⊗ᶜ nonterm expr
  restBranch mul = letter times ⊗ᶜ nonterm expr
  restBranch (pow n) = letter caret ⊗ᶜ letter (nat n) ⊗ᶜ nonterm rest
  restBranch stop = eps

  numTailBranch : QTag → Code
  numTailBranch (den m) = letter slash ⊗ᶜ letter (nat m) ⊗ᶜ nonterm rest
  numTailBranch (more t) = restBranch t

polyCode : Nt → Code
polyCode expr = ⊕e ETag exprBranch
polyCode rest = ⊕e KTag restBranch
polyCode numTail = ⊕e QTag numTailBranch

private
  sLetter : (c : Tok) → isSetValued (letter c)
  sLetter c = lift (isSetLiteral c)

  sNonterm : (n : Nt) → isSetValued (nonterm n)
  sNonterm n = lift tt*

  sEps : isSetValued eps
  sEps = lift isSetεTy

  infixr 5 _s⊗ᶜ_
  _s⊗ᶜ_ : {F G : Code} → isSetValued F → isSetValued G → isSetValued (F ⊗ᶜ G)
  sF s⊗ᶜ sG = two sF sG

  sExprBranch : (t : ETag) → isSetValued (exprBranch t)
  sExprBranch paren =
    sLetter lp s⊗ᶜ sNonterm expr s⊗ᶜ sLetter rp s⊗ᶜ sNonterm rest
  sExprBranch (atom v) = sLetter (var v) s⊗ᶜ sNonterm rest
  sExprBranch (num n) = sLetter (nat n) s⊗ᶜ sNonterm numTail
  sExprBranch neg = sLetter minus s⊗ᶜ sNonterm expr

  sRestBranch : (t : KTag) → isSetValued (restBranch t)
  sRestBranch add = sLetter plus s⊗ᶜ sNonterm expr
  sRestBranch mul = sLetter times s⊗ᶜ sNonterm expr
  sRestBranch (pow n) = sLetter caret s⊗ᶜ sLetter (nat n) s⊗ᶜ sNonterm rest
  sRestBranch stop = sEps

  sNumTailBranch : (t : QTag) → isSetValued (numTailBranch t)
  sNumTailBranch (den m) = sLetter slash s⊗ᶜ sLetter (nat m) s⊗ᶜ sNonterm rest
  sNumTailBranch (more t) = sRestBranch t

sPolyCode : (n : Nt) → isSetValued (polyCode n)
sPolyCode expr = lift isSetETag , sExprBranch
sPolyCode rest = lift isSetKTag , sRestBranch
sPolyCode numTail = lift isSetQTag , sNumTailBranch

Poly : Nt → TheoryTy ℓG tt
Poly = μ polyCode

Expr : TheoryTy ℓG tt
Expr = Poly expr

Rest : TheoryTy ℓG tt
Rest = Poly rest

NumTail : TheoryTy ℓG tt
NumTail = Poly numTail

isSetPoly : (n : Nt) → isSetTheoryTy (Poly n)
isSetPoly = isSetμ polyCode sPolyCode

-- The one unrolling, as grammars built from the combinators.  Every code
-- leaf is a `Lift`, and `⊗e` is the arity-indexed `⊗ᵘ`; `⟦⊗e⟧` and
-- `lowerTy` are what move across, one symbol at a time.

BodyExpr : ETag → TheoryTy ℓG tt
BodyExpr paren = literal lp ⊗ (Expr ⊗ (literal rp ⊗ Rest))
BodyExpr (atom v) = literal (var v) ⊗ Rest
BodyExpr (num n) = literal (nat n) ⊗ NumTail
BodyExpr neg = literal minus ⊗ Expr

BodyRest : KTag → TheoryTy ℓG tt
BodyRest add = literal plus ⊗ Expr
BodyRest mul = literal times ⊗ Expr
BodyRest (pow n) = literal caret ⊗ (literal (nat n) ⊗ Rest)
BodyRest stop = LiftTheoryTy ℓG εTy

BodyNumTail : QTag → TheoryTy ℓG tt
BodyNumTail (den m) = literal slash ⊗ (literal (nat m) ⊗ Rest)
BodyNumTail (more t) = BodyRest t

private
  out2 : (F G : Code) → ⟦ F ⊗ᶜ G ⟧TheoryTy Poly
       ⊢ ⟦ F ⟧TheoryTy Poly ⊗ ⟦ G ⟧TheoryTy Poly
  out2 F G = ⟦⊗e⟧ F G

  in2 : (F G : Code) → ⟦ F ⟧TheoryTy Poly ⊗ ⟦ G ⟧TheoryTy Poly
      ⊢ ⟦ F ⊗ᶜ G ⟧TheoryTy Poly
  in2 F G = ⟦⊗e⟧⁻ F G

exprOut : (t : ETag) → ⟦ exprBranch t ⟧TheoryTy Poly ⊢ BodyExpr t
exprOut paren =
  (lowerTy ,⊗ (lowerTy ,⊗ (lowerTy ,⊗ lowerTy)))
  ∘⊢ (id⊢ ,⊗ (id⊢ ,⊗ out2 _ _)) ∘⊢ (id⊢ ,⊗ out2 _ _) ∘⊢ out2 _ _
exprOut (atom v) = (lowerTy ,⊗ lowerTy) ∘⊢ out2 _ _
exprOut (num n) = (lowerTy ,⊗ lowerTy) ∘⊢ out2 _ _
exprOut neg = (lowerTy ,⊗ lowerTy) ∘⊢ out2 _ _

exprIn : (t : ETag) → BodyExpr t ⊢ ⟦ exprBranch t ⟧TheoryTy Poly
exprIn paren =
  in2 _ _ ∘⊢ (id⊢ ,⊗ in2 _ _) ∘⊢ (id⊢ ,⊗ (id⊢ ,⊗ in2 _ _))
  ∘⊢ (liftTy ,⊗ (liftTy ,⊗ (liftTy ,⊗ liftTy)))
exprIn (atom v) = in2 _ _ ∘⊢ (liftTy ,⊗ liftTy)
exprIn (num n) = in2 _ _ ∘⊢ (liftTy ,⊗ liftTy)
exprIn neg = in2 _ _ ∘⊢ (liftTy ,⊗ liftTy)

restOut : (t : KTag) → ⟦ restBranch t ⟧TheoryTy Poly ⊢ BodyRest t
restOut add = (lowerTy ,⊗ lowerTy) ∘⊢ out2 _ _
restOut mul = (lowerTy ,⊗ lowerTy) ∘⊢ out2 _ _
restOut (pow n) =
  (lowerTy ,⊗ (lowerTy ,⊗ lowerTy)) ∘⊢ (id⊢ ,⊗ out2 _ _) ∘⊢ out2 _ _
restOut stop = liftTy ∘⊢ lowerTy

restIn : (t : KTag) → BodyRest t ⊢ ⟦ restBranch t ⟧TheoryTy Poly
restIn add = in2 _ _ ∘⊢ (liftTy ,⊗ liftTy)
restIn mul = in2 _ _ ∘⊢ (liftTy ,⊗ liftTy)
restIn (pow n) =
  in2 _ _ ∘⊢ (id⊢ ,⊗ in2 _ _) ∘⊢ (liftTy ,⊗ (liftTy ,⊗ liftTy))
restIn stop = liftTy ∘⊢ lowerTy

numTailOut : (t : QTag) → ⟦ numTailBranch t ⟧TheoryTy Poly ⊢ BodyNumTail t
numTailOut (den m) =
  (lowerTy ,⊗ (lowerTy ,⊗ lowerTy)) ∘⊢ (id⊢ ,⊗ out2 _ _) ∘⊢ out2 _ _
numTailOut (more t) = restOut t

numTailIn : (t : QTag) → BodyNumTail t ⊢ ⟦ numTailBranch t ⟧TheoryTy Poly
numTailIn (den m) =
  in2 _ _ ∘⊢ (id⊢ ,⊗ in2 _ _) ∘⊢ (liftTy ,⊗ (liftTy ,⊗ liftTy))
numTailIn (more t) = restIn t

rollExpr : (t : ETag) → BodyExpr t ⊢ Expr
rollExpr t = roll ∘⊢ σ⊕ t ∘⊢ exprIn t

unrollExpr : Expr ⊢ ⊕[ t ∈ ETag ] BodyExpr t
unrollExpr = ⊕ᴰ-elim (λ t → σ⊕ t ∘⊢ exprOut t) ∘⊢ unroll polyCode expr

rollRest : (t : KTag) → BodyRest t ⊢ Rest
rollRest t = roll ∘⊢ σ⊕ t ∘⊢ restIn t

unrollRest : Rest ⊢ ⊕[ t ∈ KTag ] BodyRest t
unrollRest = ⊕ᴰ-elim (λ t → σ⊕ t ∘⊢ restOut t) ∘⊢ unroll polyCode rest

rollNumTail : (t : QTag) → BodyNumTail t ⊢ NumTail
rollNumTail t = roll ∘⊢ σ⊕ t ∘⊢ numTailIn t

unrollNumTail : NumTail ⊢ ⊕[ t ∈ QTag ] BodyNumTail t
unrollNumTail =
  ⊕ᴰ-elim (λ t → σ⊕ t ∘⊢ numTailOut t) ∘⊢ unroll polyCode numTail

ExprSet : TheorySet ℓG tt
ExprSet = Expr , isSetPoly expr

RestSet : TheorySet ℓG tt
RestSet = Rest , isSetPoly rest

NumTailSet : TheorySet ℓG tt
NumTailSet = NumTail , isSetPoly numTail

-- The route tables.  These are the whole content of "the grammar is
-- LL(1)", and they are answer-free: a table is a table at every answer.
--
-- `E` routes on one token outright, because every `ETag` is *determined*
-- by the token that starts its production -- `atom v` by `var v`, `num n`
-- by `nat n`.  `K` and `Q` do not: `pow n` and `den m` carry a numeral
-- from the *second* token, so no `M₁ → Maybe KTag` exists.  The repair is
-- left-factoring, not lookahead: route on the head (`caret`, `slash`) and
-- route *again*, over `ℕ`, on the numeral that follows.  `PowSet` is that
-- inner sum.

open import Cubical.Data.Maybe using (Maybe ; just ; nothing)

decℕEq : DiscreteEq ℕ
decℕEq = _≟ℕ_

decUnitEq : DiscreteEq Unit
decUnitEq _ _ = Sum.inl Eq.refl

private
  ⊎injL : {A B : Type ℓ-zero} {a a' : A}
    → (a Eq.≡ a') Sum.⊎ ((a Eq.≡ a') → Empty.⊥)
    → (Sum.inl {B = B} a Eq.≡ Sum.inl a')
      Sum.⊎ ((Sum.inl {B = B} a Eq.≡ Sum.inl a') → Empty.⊥)
  ⊎injL (Sum.inl Eq.refl) = Sum.inl Eq.refl
  ⊎injL (Sum.inr ne) = Sum.inr λ where Eq.refl → ne Eq.refl

  ⊎injR : {A B : Type ℓ-zero} {b b' : B}
    → (b Eq.≡ b') Sum.⊎ ((b Eq.≡ b') → Empty.⊥)
    → (Sum.inr {A = A} b Eq.≡ Sum.inr b')
      Sum.⊎ ((Sum.inr {A = A} b Eq.≡ Sum.inr b') → Empty.⊥)
  ⊎injR (Sum.inl Eq.refl) = Sum.inl Eq.refl
  ⊎injR (Sum.inr ne) = Sum.inr λ where Eq.refl → ne Eq.refl

dec⊎Eq : {A B : Type ℓ-zero}
  → DiscreteEq A → DiscreteEq B → DiscreteEq (A ⊎ B)
dec⊎Eq dA dB (Sum.inl a) (Sum.inl a') = ⊎injL (dA a a')
dec⊎Eq dA dB (Sum.inl a) (Sum.inr b) = Sum.inr λ ()
dec⊎Eq dA dB (Sum.inr b) (Sum.inl a) = Sum.inr λ ()
dec⊎Eq dA dB (Sum.inr b) (Sum.inr b') = ⊎injR (dB b b')

decVEq : DiscreteEq V
decVEq = _≟V_

decETag : DiscreteEq ETag
decETag = dec⊎Eq decUnitEq (dec⊎Eq decVEq (dec⊎Eq decℕEq decUnitEq))

-- The heads.  `KH` is `KTag` with the exponent's numeral factored out and
-- the ε-production dropped -- what one token can name.  `QH` adds the
-- denominator's head.

data KH : Type ℓ-zero where
  hadd hmul hpow : KH

decKH : DiscreteEq KH
decKH hadd hadd = Sum.inl Eq.refl
decKH hmul hmul = Sum.inl Eq.refl
decKH hpow hpow = Sum.inl Eq.refl
decKH hadd hmul = Sum.inr λ () ; decKH hadd hpow = Sum.inr λ ()
decKH hmul hadd = Sum.inr λ () ; decKH hmul hpow = Sum.inr λ ()
decKH hpow hadd = Sum.inr λ () ; decKH hpow hmul = Sum.inr λ ()

QH : Type ℓ-zero
QH = Unit ⊎ KH

pattern qden = Sum.inl tt
pattern qmore h = Sum.inr h

decQH : DiscreteEq QH
decQH = dec⊎Eq decUnitEq decKH

-- The branch families, as sets: `ty (CE t)` is `BodyExpr t` on the nose.

NatBr : ℕ → TheorySet ℓG tt
NatBr n = litSet (nat n) ⊗Set RestSet

PowSet : TheorySet ℓG tt
PowSet = ⊕ᴰSet (DiscreteEq→isSet decℕEq) NatBr

CE : ETag → TheorySet ℓG tt
CE paren = litSet lp ⊗Set (ExprSet ⊗Set (litSet rp ⊗Set RestSet))
CE (atom v) = litSet (var v) ⊗Set RestSet
CE (num n) = litSet (nat n) ⊗Set NumTailSet
CE neg = litSet minus ⊗Set ExprSet

CK : KH → TheorySet ℓG tt
CK hadd = litSet plus ⊗Set ExprSet
CK hmul = litSet times ⊗Set ExprSet
CK hpow = litSet caret ⊗Set PowSet

CQ : QH → TheorySet ℓG tt
CQ qden = litSet slash ⊗Set PowSet
CQ (qmore h) = CK h

rE : M₁ → Maybe ETag
rE (tk lp) = just paren
rE (tk (var v)) = just (atom v)
rE (tk (nat n)) = just (num n)
rE (tk minus) = just neg
rE _ = nothing

rK : M₁ → Maybe KH
rK (tk plus) = just hadd
rK (tk times) = just hmul
rK (tk caret) = just hpow
rK _ = nothing

rQ : M₁ → Maybe QH
rQ (tk slash) = just qden
rQ (tk plus) = just (qmore hadd)
rQ (tk times) = just (qmore hmul)
rQ (tk caret) = just (qmore hpow)
rQ _ = nothing

rNat : M₁ → Maybe ℕ
rNat (tk (nat n)) = just n
rNat _ = nothing

-- Every `into` is the same three steps: reassociate the continuation out,
-- forget everything but the leading letter, and name the cell.

GuideOf : {Y : Type ℓ-zero} (C : Y → TheorySet ℓG tt) → Type _
GuideOf C = (K : TheorySet ℓG tt) → Route (λ y → ty (C y) ⊗ ty K) ℓG

private
  lead : {A : TheoryTy ℓG tt} {K : TheoryTy ℓG tt} (c : Tok)
    → (literal c ⊗ A) ⊗ K ⊢ Λ₁ (tk c)
  lead c = (id⊢ ,⊗ ⊤Ty-intro) ∘⊢ ⊗-assoc

gE : GuideOf CE
gE K .Route.B = Push.PB ℓG rE
gE K .Route.cov = Push.covers ℓG rE
gE K .Route.into paren = Push.atCell ℓG rE (tk lp) ∘⊢ lead lp
gE K .Route.into (atom v) = Push.atCell ℓG rE (tk (var v)) ∘⊢ lead (var v)
gE K .Route.into (num n) = Push.atCell ℓG rE (tk (nat n)) ∘⊢ lead (nat n)
gE K .Route.into neg = Push.atCell ℓG rE (tk minus) ∘⊢ lead minus

gK : GuideOf CK
gK K .Route.B = Push.PB ℓG rK
gK K .Route.cov = Push.covers ℓG rK
gK K .Route.into hadd = Push.atCell ℓG rK (tk plus) ∘⊢ lead plus
gK K .Route.into hmul = Push.atCell ℓG rK (tk times) ∘⊢ lead times
gK K .Route.into hpow = Push.atCell ℓG rK (tk caret) ∘⊢ lead caret

gQ : GuideOf CQ
gQ K .Route.B = Push.PB ℓG rQ
gQ K .Route.cov = Push.covers ℓG rQ
gQ K .Route.into qden = Push.atCell ℓG rQ (tk slash) ∘⊢ lead slash
gQ K .Route.into (qmore hadd) = Push.atCell ℓG rQ (tk plus) ∘⊢ lead plus
gQ K .Route.into (qmore hmul) = Push.atCell ℓG rQ (tk times) ∘⊢ lead times
gQ K .Route.into (qmore hpow) = Push.atCell ℓG rQ (tk caret) ∘⊢ lead caret

gN : GuideOf NatBr
gN K .Route.B = Push.PB ℓG rNat
gN K .Route.cov = Push.covers ℓG rNat
gN K .Route.into n = Push.atCell ℓG rNat (tk (nat n)) ∘⊢ lead (nat n)

-- Gluing the routed sum back onto the grammar's own `⊕ᴰ`.  `E` is an
-- exact relabelling; `K` and `Q` are the sum of their non-nullable heads
-- *plus* the ε-production, and the `pow`/`den` heads redistribute their
-- inner `⊕[ n ∈ ℕ ]` across the leading letter.

rollE : (⊕[ t ∈ ETag ] ty (CE t)) ⊢ Expr
rollE = ⊕ᴰ-elim br
  where
  br : (t : ETag) → ty (CE t) ⊢ Expr
  br paren = rollExpr paren
  br (atom v) = rollExpr (atom v)
  br (num n) = rollExpr (num n)
  br neg = rollExpr neg

unrollE : Expr ⊢ (⊕[ t ∈ ETag ] ty (CE t))
unrollE = ⊕ᴰ-elim br ∘⊢ unrollExpr
  where
  br : (t : ETag) → BodyExpr t ⊢ (⊕[ t ∈ ETag ] ty (CE t))
  br paren = σ⊕ paren
  br (atom v) = σ⊕ (atom v)
  br (num n) = σ⊕ (num n)
  br neg = σ⊕ neg

rollK : ((⊕[ y ∈ KH ] ty (CK y)) ⊕ ty (ε↑Set ℓG)) ⊢ Rest
rollK = ⊕-elim (⊕ᴰ-elim br) (rollRest stop)
  where
  br : (y : KH) → ty (CK y) ⊢ Rest
  br hadd = rollRest add
  br hmul = rollRest mul
  br hpow = ⊕ᴰ-elim (λ n → rollRest (pow n)) ∘⊢ ⊗⊕ᴰ-distR

unrollK : Rest ⊢ ((⊕[ y ∈ KH ] ty (CK y)) ⊕ ty (ε↑Set ℓG))
unrollK = ⊕ᴰ-elim br ∘⊢ unrollRest
  where
  br : (t : KTag) → BodyRest t ⊢ ((⊕[ y ∈ KH ] ty (CK y)) ⊕ ty (ε↑Set ℓG))
  br add = inl ∘⊢ σ⊕ hadd
  br mul = inl ∘⊢ σ⊕ hmul
  br (pow n) = inl ∘⊢ σ⊕ hpow ∘⊢ (id⊢ ,⊗ σ⊕ n)
  br stop = inr

rollQ : ((⊕[ y ∈ QH ] ty (CQ y)) ⊕ ty (ε↑Set ℓG)) ⊢ NumTail
rollQ = ⊕-elim (⊕ᴰ-elim br) (rollNumTail (more stop))
  where
  br : (y : QH) → ty (CQ y) ⊢ NumTail
  br qden = ⊕ᴰ-elim (λ m → rollNumTail (den m)) ∘⊢ ⊗⊕ᴰ-distR
  br (qmore hadd) = rollNumTail (more add)
  br (qmore hmul) = rollNumTail (more mul)
  br (qmore hpow) =
    ⊕ᴰ-elim (λ n → rollNumTail (more (pow n))) ∘⊢ ⊗⊕ᴰ-distR

unrollQ : NumTail ⊢ ((⊕[ y ∈ QH ] ty (CQ y)) ⊕ ty (ε↑Set ℓG))
unrollQ = ⊕ᴰ-elim br ∘⊢ unrollNumTail
  where
  br : (t : QTag)
    → BodyNumTail t ⊢ ((⊕[ y ∈ QH ] ty (CQ y)) ⊕ ty (ε↑Set ℓG))
  br (den m) = inl ∘⊢ σ⊕ qden ∘⊢ (id⊢ ,⊗ σ⊕ m)
  br (more add) = inl ∘⊢ σ⊕ (qmore hadd)
  br (more mul) = inl ∘⊢ σ⊕ (qmore hmul)
  br (more (pow n)) = inl ∘⊢ σ⊕ (qmore hpow) ∘⊢ (id⊢ ,⊗ σ⊕ n)
  br (more stop) = inr
