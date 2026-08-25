{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Parenthesised multivariate polynomials, as a grammar for the combinator
   library.  Variables are drawn from any discrete `V`; a variable, a
   numeral and an exponent are each one token, so nothing here lexes.

     E ::= ( E ) K | v K | n Q | - E
     Q ::= / m K | + E | * E | ^ n K | ε
     K ::=         + E | * E | ^ n K | ε

   `n / m` is the rational scalar -- a fraction of two naturals -- and `- E`
   is what makes it (and anything else) negative.  `^ n` is exponentiation
   by a natural: the exponent is a numeral *token*, not an expression, so
   `x ^ (y + 1)` is not a word of the language.

   Two things fix this shape.

   First, every production begins with a terminal.  That is forced, not
   stylistic: `call` answers only at *proper* suffixes, so a production
   whose first symbol is a nonterminal has nothing to pay for the recursive
   call.  The usual `E ::= T E'` factoring is therefore inlined, which is
   also why `K` carries every operator rather than one precedence level.
   Both operators associate to the right and neither binds tighter, so
   precedence is what the parentheses are for.

   Second, the grammar is left-factored, so one token decides every
   production.  Writing the scalar as a production `n / m K` beside `n K`
   would not be: both begin with `nat n`, and it takes a second token to
   say which.  `Q` is the tail after a numeral -- a denominator, or
   whatever `K` would have done -- so `QTag` is literally `ℕ ⊎ KTag` and
   `Q`'s non-denominator half *is* `K`'s.  FIRST(Q) = {/,+,*,^} and
   FOLLOW(Q) = FOLLOW(K) = FOLLOW(E) = {`)`, end}, which are disjoint, so
   the ε-production is decided too.

   The grammar is a functor and nothing more: `μ` of `polyCode`.  There is
   no `Grammar` record and no production list, so the tags need only be
   sets -- their decidability is the parser's business, not the grammar's.

   This file stops at the `TheorySet`s.  What follows in `Dyck` is the
   parser, and that is the exercise. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open import Cubical.Data.Sum as Sum using (_⊎_)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Decidable.Polynomial
  (V : Type ℓ-zero)
  (_≟V_ : (a b : V) → (a Eq.≡ b) Sum.⊎ ((a Eq.≡ b) → Empty.⊥))
  where

open import Cubical.Data.Sum.Properties using (isSet⊎)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Unit using (Unit ; tt ; tt* ; isSetUnit)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Properties using (isSetℕ ; discreteℕ)
open import Cubical.Relation.Nullary.Base using (Discrete ; decRec ; yes ; no)
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)

------------------------------------------------------------------------
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
  -- decidable equality on `ℕ`, in the form the combinators ask for
  _≟ℕ_ : (a b : ℕ) → (a Eq.≡ b) Sum.⊎ ((a Eq.≡ b) → Empty.⊥)
  _≟ℕ_ a b = decRec (λ p → Sum.inl (Eq.pathToEq p))
                    (λ ¬p → Sum.inr λ q → ¬p (Eq.eqToPath q)) (discreteℕ a b)

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
var v ≟ var w = go (v ≟V w)
  where
  go : (v Eq.≡ w) Sum.⊎ ((v Eq.≡ w) → Empty.⊥)
     → (var v Eq.≡ var w) Sum.⊎ ((var v Eq.≡ var w) → Empty.⊥)
  go (Sum.inl Eq.refl) = Sum.inl Eq.refl
  go (Sum.inr ne) = Sum.inr λ where Eq.refl → ne Eq.refl
nat n ≟ nat n' = go (n ≟ℕ n')
  where
  go : (n Eq.≡ n') Sum.⊎ ((n Eq.≡ n') → Empty.⊥)
     → (nat n Eq.≡ nat n') Sum.⊎ ((nat n Eq.≡ nat n') → Empty.⊥)
  go (Sum.inl Eq.refl) = Sum.inl Eq.refl
  go (Sum.inr ne) = Sum.inr λ where Eq.refl → ne Eq.refl
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

-- the continuation level: the one `μ` lands at
open import Theory.Instances.Monoid.Combinator.Decidable.Base Tok _≟_ (ℓ-suc ℓ-zero)
open import Theory.Instances.Monoid.Residual Tok isSetAlphabet
  using (⟦⊗e⟧ ; ⟦⊗e⟧⁻)

------------------------------------------------------------------------
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

------------------------------------------------------------------------
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

  -- ...and `Q`'s, which are `K`'s but for the denominator
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

------------------------------------------------------------------------
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

------------------------------------------------------------------------
-- ...and the three grammars carrying their h-level, which is what a parser
-- is indexed by.  From here on it is `seq`, `tok`, `_<|>_`, `nil`, `call`
-- and `fix`, as in `Dyck`: three mutually recursive parsers, one per
-- nonterminal, tied by Löb at their `&ᴰ`.

ExprSet : TheorySet ℓG tt
ExprSet = Expr , isSetPoly expr

RestSet : TheorySet ℓG tt
RestSet = Rest , isSetPoly rest

NumTailSet : TheorySet ℓG tt
NumTailSet = NumTail , isSetPoly numTail
