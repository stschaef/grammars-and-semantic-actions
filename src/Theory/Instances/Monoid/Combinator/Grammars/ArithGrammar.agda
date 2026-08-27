{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Arithmetic expressions: the alphabet, the grammar and its route table.

   Nothing here mentions an answer.  `Grammars/Arith` is the parser over it,
   parametric in one; this file is what that parser is parametric *over*.

     Exp  ::= nm Exp' | ( Exp ) Exp'
     Exp' ::= ε | + Exp

   Every production begins with a terminal, so one token names the `Exp`
   production -- that naming is `rExp`, and `gExp` is the route it induces
   on the one-token cover. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Grammars.ArithGrammar where

open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)

-- The alphabet

data Tok : Type where
  nm pl lb rb : Tok

_≟T_ : (x y : Tok) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
nm ≟T nm = Sum.inl Eq.refl
pl ≟T pl = Sum.inl Eq.refl
lb ≟T lb = Sum.inl Eq.refl
rb ≟T rb = Sum.inl Eq.refl
nm ≟T pl = Sum.inr λ () ; nm ≟T lb = Sum.inr λ () ; nm ≟T rb = Sum.inr λ ()
pl ≟T nm = Sum.inr λ () ; pl ≟T lb = Sum.inr λ () ; pl ≟T rb = Sum.inr λ ()
lb ≟T nm = Sum.inr λ () ; lb ≟T pl = Sum.inr λ () ; lb ≟T rb = Sum.inr λ ()
rb ≟T nm = Sum.inr λ () ; rb ≟T pl = Sum.inr λ () ; rb ≟T lb = Sum.inr λ ()

open import Theory.Instances.Monoid.Combinator.Core Tok _≟T_ public
  hiding (Maybe ; just ; nothing)
open import Theory.Instances.Monoid.Residual Tok isSetAlphabet
  using (⟦⊗e⟧ ; ⟦⊗e⟧⁻)

ℓG : Level
ℓG = ℓ-max ℓM (ℓ-suc ℓ-zero)

-- The grammar

data NT : Type ℓ-zero where
  Exp Exp' : NT

data Tag : NT → Type ℓ-zero where
  enum eparen : Tag Exp
  done add    : Tag Exp'

Code : Type _
Code = Functor ℓM NT (λ _ → tt) tt

infixr 20 _⊗c_
_⊗c_ : Code → Code → Code
F ⊗c G = ⊗e _⊙_ (two F G)

body : (N : NT) → Tag N → Code
body Exp  enum   = k (literal nm) ⊗c Var Exp'
body Exp  eparen = ((k (literal lb) ⊗c Var Exp) ⊗c k (literal rb)) ⊗c Var Exp'
body Exp' done   = k εTy
body Exp' add    = k (literal pl) ⊗c Var Exp

Arith : (N : NT) → Code
Arith N = ⊕e (Tag N) (body N)

decTag : (N : NT) → DiscreteEq (Tag N)
decTag Exp  enum   enum   = Sum.inl Eq.refl
decTag Exp  eparen eparen = Sum.inl Eq.refl
decTag Exp  enum   eparen = Sum.inr λ ()
decTag Exp  eparen enum   = Sum.inr λ ()
decTag Exp' done done = Sum.inl Eq.refl
decTag Exp' add  add  = Sum.inl Eq.refl
decTag Exp' done add  = Sum.inr λ ()
decTag Exp' add  done = Sum.inr λ ()

isSetTag : (N : NT) → isSet (Tag N)
isSetTag N = Discrete→isSet λ t u → Sum.rec
  (λ p → yes (Eq.eqToPath p)) (λ ¬p → no λ p → ¬p (Eq.pathToEq p)) (decTag N t u)
  where open import Cubical.Relation.Nullary.Base using (yes ; no)
        open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)

isSetArith : (N : NT) → isSetValued (Arith N)
isSetArith N = lift (isSetTag N) , br N
  where
  isSetLit : (c : Tok) → isSetValued {X = Tok} {xs = λ _ → tt} (k (literal c))
  isSetLit c = lift (isSetLiteral c)

  br : (N : NT) (t : Tag N) → isSetValued (body N t)
  br Exp enum = λ where
    zero → isSetLit nm
    (suc zero) → lift tt*
  br Exp eparen = λ where
    zero → λ where
      zero → λ where
        zero → isSetLit lb
        (suc zero) → lift tt*
      (suc zero) → isSetLit rb
    (suc zero) → lift tt*
  br Exp' done = lift isSetεTy
  br Exp' add  = λ where
    zero → isSetLit pl
    (suc zero) → lift tt*

Lang : NT → TheoryTy _ tt
Lang = μ Arith

LangSet : NT → TheorySet ℓG tt
LangSet N = Lang N , isSetμ Arith isSetArith N

lit↑ : Tok → TheorySet ℓG tt
lit↑ c = LiftTheoryTy ℓG (literal c) , isSetLiftTheoryTy (isSetLiteral c)

Cb : (N : NT) → Tag N → TheorySet ℓG tt
Cb Exp  enum   = lit↑ nm ⊗Set LangSet Exp'
Cb Exp  eparen = ((lit↑ lb ⊗Set LangSet Exp) ⊗Set lit↑ rb) ⊗Set LangSet Exp'
Cb Exp' done   = ε↑Set ℓG
Cb Exp' add    = lit↑ pl ⊗Set LangSet Exp

bodyIn : (N : NT) (t : Tag N) → ty (Cb N t) ⊢ ⟦ body N t ⟧TheoryTy Lang
bodyIn Exp enum = ⟦⊗e⟧⁻ _ _ ∘⊢ ((liftTy ∘⊢ lowerTy) ,⊗ liftTy)
bodyIn Exp eparen =
  ⟦⊗e⟧⁻ _ _ ∘⊢ ((⟦⊗e⟧⁻ _ _ ∘⊢ ((⟦⊗e⟧⁻ _ _
    ∘⊢ ((liftTy ∘⊢ lowerTy) ,⊗ liftTy)) ,⊗ (liftTy ∘⊢ lowerTy))) ,⊗ liftTy)
bodyIn Exp' done = liftTy ∘⊢ lowerTy
bodyIn Exp' add  = ⟦⊗e⟧⁻ _ _ ∘⊢ ((liftTy ∘⊢ lowerTy) ,⊗ liftTy)

bodyOut : (N : NT) (t : Tag N) → ⟦ body N t ⟧TheoryTy Lang ⊢ ty (Cb N t)
bodyOut Exp enum = ((liftTy ∘⊢ lowerTy) ,⊗ lowerTy) ∘⊢ ⟦⊗e⟧ _ _
bodyOut Exp eparen =
  ((((((liftTy ∘⊢ lowerTy) ,⊗ lowerTy) ∘⊢ ⟦⊗e⟧ _ _) ,⊗ (liftTy ∘⊢ lowerTy))
    ∘⊢ ⟦⊗e⟧ _ _) ,⊗ lowerTy) ∘⊢ ⟦⊗e⟧ _ _
bodyOut Exp' done = liftTy ∘⊢ lowerTy
bodyOut Exp' add  = ((liftTy ∘⊢ lowerTy) ,⊗ lowerTy) ∘⊢ ⟦⊗e⟧ _ _

rollN : (N : NT) → (⊕[ t ∈ Tag N ] ty (Cb N t)) ⊢ Lang N
rollN N = roll ∘⊢ ⊕ᴰ-elim λ t → σ⊕ t ∘⊢ bodyIn N t

unrollN : (N : NT) → Lang N ⊢ (⊕[ t ∈ Tag N ] ty (Cb N t))
unrollN N = ⊕ᴰ-elim (λ t → σ⊕ t ∘⊢ bodyOut N t) ∘⊢ unroll Arith N

-- The route.  `rExp` is the LL(1) table for `Exp`, and `gExp` is the
-- coarsening of the one-token cover along it -- both answer-free, which is
-- the point: a table is a table at every answer.

rExp : M₁ → Maybe (Tag Exp)
rExp (tk nm) = just enum
rExp (tk lb) = just eparen
rExp _ = nothing

-- the type a `Choice.Guide` unfolds to, stated without the answer
GuideOf : {Y : Type ℓ-zero} (C : Y → TheorySet ℓG tt) → Type _
GuideOf C = (K : TheorySet ℓG tt) → Route (λ y → ty (C y) ⊗ ty K) ℓG

gExp : GuideOf (Cb Exp)
gExp K .Route.B = Push.PB ℓG rExp
gExp K .Route.cov = Push.covers ℓG rExp
gExp K .Route.into enum =
  Push.atCell ℓG rExp (tk nm) ∘⊢ (lowerTy ,⊗ ⊤Ty-intro) ∘⊢ ⊗-assoc
gExp K .Route.into eparen =
  Push.atCell ℓG rExp (tk lb) ∘⊢ (lowerTy ,⊗ ⊤Ty-intro)
  ∘⊢ ⊗-assoc ∘⊢ ⊗-assoc ∘⊢ ⊗-assoc
