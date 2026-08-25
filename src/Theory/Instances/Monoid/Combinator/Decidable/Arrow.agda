{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Parsing functions and parenthesised member access.

     E ::= '(' Q '=>' E            -- arrow function; Q swallows its ')'
         | '(' E ')' '.' id        -- member access
         | id
     Q ::= id ')' | id ',' Q

   This is LL(*), as the two bracket production share an unbounded prefix.
   We parse it using arbitrarily long lookahead
-}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Decidable.Arrow where

open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; _×_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)

open import Theory.Instances.Monoid.Combinator.Decidable.Bracket
open import Theory.Instances.Monoid.Combinator.Decidable.Window Tok _≟T_ (ℓ-suc ℓ-zero)
open import Theory.Instances.Monoid.Residual Tok isSetAlphabet
  using (⟦⊗e⟧ ; ⟦⊗e⟧⁻)

data NT : Type ℓ-zero where
  E Q : NT

data Tg : NT → Type ℓ-zero where
  arrow member idT : Tg E
  one cons         : Tg Q

decTg : (N : NT) → DiscreteEq (Tg N)
decTg E arrow  arrow  = Sum.inl Eq.refl
decTg E member member = Sum.inl Eq.refl
decTg E idT    idT    = Sum.inl Eq.refl
decTg E arrow  member = Sum.inr λ ()
decTg E arrow  idT    = Sum.inr λ ()
decTg E member arrow  = Sum.inr λ ()
decTg E member idT    = Sum.inr λ ()
decTg E idT    arrow  = Sum.inr λ ()
decTg E idT    member = Sum.inr λ ()
decTg Q one  one  = Sum.inl Eq.refl
decTg Q cons cons = Sum.inl Eq.refl
decTg Q one  cons = Sum.inr λ ()
decTg Q cons one  = Sum.inr λ ()

isSetTg : (N : NT) → isSet (Tg N)
isSetTg N = Discrete→isSet λ t u → Sum.rec
  (λ p → yes (Eq.eqToPath p)) (λ ¬p → no λ p → ¬p (Eq.pathToEq p)) (decTg N t u)
  where open import Cubical.Relation.Nullary.Base using (yes ; no)
        open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)

Code : Type _
Code = Functor ℓM NT (λ _ → tt) tt

infixr 20 _⊗c_
_⊗c_ : Code → Code → Code
F ⊗c G = ⊗e _⊙_ (two F G)

body : (N : NT) → Tg N → Code
body E arrow  = k (literal lp) ⊗c Var Q ⊗c k (literal ar) ⊗c Var E
body E member = k (literal lp) ⊗c Var E ⊗c k (literal rp) ⊗c k (literal dot)
                  ⊗c k (literal vid)
body E idT    = k (literal vid)
body Q one    = k (literal vid) ⊗c k (literal rp)
body Q cons   = k (literal vid) ⊗c k (literal cm) ⊗c Var Q

Sys : (N : NT) → Code
Sys N = ⊕e (Tg N) (body N)

isSetSys : (N : NT) → isSetValued (Sys N)
isSetSys N = lift (isSetTg N) , br N
  where
  sl : (c : Tok) → isSetValued {X = NT} {xs = λ _ → tt} (k (literal c))
  sl c = lift (isSetLiteral c)

  br : (N : NT) (t : Tg N) → isSetValued (body N t)
  br E arrow = λ where
    zero → sl lp
    (suc zero) → λ where
      zero → lift tt*
      (suc zero) → λ where
        zero → sl ar
        (suc zero) → lift tt*
  br E member = λ where
    zero → sl lp
    (suc zero) → λ where
      zero → lift tt*
      (suc zero) → λ where
        zero → sl rp
        (suc zero) → λ where
          zero → sl dot
          (suc zero) → sl vid
  br E idT = sl vid
  br Q one = λ where
    zero → sl vid
    (suc zero) → sl rp
  br Q cons = λ where
    zero → sl vid
    (suc zero) → λ where
      zero → sl cm
      (suc zero) → lift tt*

Lang : NT → TheoryTy _ tt
Lang = μ Sys

LangSet : NT → TheorySet ℓG tt
LangSet N = Lang N , isSetμ Sys isSetSys N

Tr : NT → TheoryTy ℓ-zero tt
Tr E = TranspG
Tr Q = ClosG

transpAll : (N : NT) → Lang N ⊢ Tr N
transpAll = rec Sys alg
  where
  br : (N : NT) (t : Tg N) → ⟦ body N t ⟧TheoryTy Tr ⊢ Tr N
  br E idT = tr-lit vid tt ∘⊢ lowerTy
  br E arrow =
    tr-open
    ∘⊢ (lowerTy ,⊗ ((lowerTy ,⊗
          (tr-skip ar tt ∘⊢ (lowerTy ,⊗ lowerTy) ∘⊢ ⟦⊗e⟧ _ _)) ∘⊢ ⟦⊗e⟧ _ _))
    ∘⊢ ⟦⊗e⟧ _ _
  br E member =
    tr-wrap
    ∘⊢ (lowerTy ,⊗ ((lowerTy ,⊗ ((lowerTy ,⊗
          (tr-skip dot tt ∘⊢ (lowerTy ,⊗ (tr-lit vid tt ∘⊢ lowerTy))
            ∘⊢ ⟦⊗e⟧ _ _)) ∘⊢ ⟦⊗e⟧ _ _)) ∘⊢ ⟦⊗e⟧ _ _))
    ∘⊢ ⟦⊗e⟧ _ _
  br Q one = cl-skip vid tt ∘⊢ (lowerTy ,⊗ (cl-rp ∘⊢ lowerTy)) ∘⊢ ⟦⊗e⟧ _ _
  br Q cons =
    cl-skip vid tt
    ∘⊢ (lowerTy ,⊗ (cl-skip cm tt ∘⊢ (lowerTy ,⊗ lowerTy) ∘⊢ ⟦⊗e⟧ _ _))
    ∘⊢ ⟦⊗e⟧ _ _

  alg : (N : NT) → ⟦ Sys N ⟧TheoryTy Tr ⊢ Tr N
  alg N = ⊕ᴰ-elim (br N)

lit↑ : Tok → TheorySet ℓG tt
lit↑ c = LiftTheoryTy ℓG (literal c) , isSetLiftTheoryTy (isSetLiteral c)

Cb : (N : NT) → Tg N → TheorySet ℓG tt
Cb E arrow  = lit↑ lp ⊗Set (LangSet Q ⊗Set (lit↑ ar ⊗Set LangSet E))
Cb E member =
  lit↑ lp ⊗Set (LangSet E ⊗Set (lit↑ rp ⊗Set (lit↑ dot ⊗Set lit↑ vid)))
Cb E idT    = lit↑ vid
Cb Q one    = lit↑ vid ⊗Set lit↑ rp
Cb Q cons   = lit↑ vid ⊗Set (lit↑ cm ⊗Set LangSet Q)

bodyIn : (N : NT) (t : Tg N) → ty (Cb N t) ⊢ ⟦ body N t ⟧TheoryTy Lang
bodyIn E arrow =
  ⟦⊗e⟧⁻ _ _ ∘⊢ ((liftTy ∘⊢ lowerTy) ,⊗ (⟦⊗e⟧⁻ _ _ ∘⊢ (liftTy ,⊗ (⟦⊗e⟧⁻ _ _ ∘⊢ ((liftTy ∘⊢ lowerTy) ,⊗ liftTy)))))
bodyIn E member =
  ⟦⊗e⟧⁻ _ _ ∘⊢ ((liftTy ∘⊢ lowerTy) ,⊗ (⟦⊗e⟧⁻ _ _ ∘⊢ (liftTy ,⊗ (⟦⊗e⟧⁻ _ _
    ∘⊢ ((liftTy ∘⊢ lowerTy) ,⊗ (⟦⊗e⟧⁻ _ _ ∘⊢ ((liftTy ∘⊢ lowerTy) ,⊗ (liftTy ∘⊢ lowerTy))))))))
bodyIn E idT = liftTy ∘⊢ lowerTy
bodyIn Q one = ⟦⊗e⟧⁻ _ _ ∘⊢ ((liftTy ∘⊢ lowerTy) ,⊗ (liftTy ∘⊢ lowerTy))
bodyIn Q cons = ⟦⊗e⟧⁻ _ _ ∘⊢ ((liftTy ∘⊢ lowerTy) ,⊗ (⟦⊗e⟧⁻ _ _ ∘⊢ ((liftTy ∘⊢ lowerTy) ,⊗ liftTy)))

bodyOut : (N : NT) (t : Tg N) → ⟦ body N t ⟧TheoryTy Lang ⊢ ty (Cb N t)
bodyOut E arrow =
  ((liftTy ∘⊢ lowerTy) ,⊗ ((lowerTy ,⊗ (((liftTy ∘⊢ lowerTy) ,⊗ lowerTy) ∘⊢ ⟦⊗e⟧ _ _)) ∘⊢ ⟦⊗e⟧ _ _)) ∘⊢ ⟦⊗e⟧ _ _
bodyOut E member =
  ((liftTy ∘⊢ lowerTy) ,⊗ ((lowerTy ,⊗ (((liftTy ∘⊢ lowerTy) ,⊗ (((liftTy ∘⊢ lowerTy) ,⊗ (liftTy ∘⊢ lowerTy)) ∘⊢ ⟦⊗e⟧ _ _)) ∘⊢ ⟦⊗e⟧ _ _))
    ∘⊢ ⟦⊗e⟧ _ _)) ∘⊢ ⟦⊗e⟧ _ _
bodyOut E idT = (liftTy ∘⊢ lowerTy)
bodyOut Q one = ((liftTy ∘⊢ lowerTy) ,⊗ (liftTy ∘⊢ lowerTy)) ∘⊢ ⟦⊗e⟧ _ _
bodyOut Q cons = ((liftTy ∘⊢ lowerTy) ,⊗ (((liftTy ∘⊢ lowerTy) ,⊗ lowerTy) ∘⊢ ⟦⊗e⟧ _ _)) ∘⊢ ⟦⊗e⟧ _ _

rollN : (N : NT) → (⊕[ t ∈ Tg N ] ty (Cb N t)) ⊢ Lang N
rollN N = roll ∘⊢ ⊕ᴰ-elim λ t → σ⊕ t ∘⊢ bodyIn N t

unrollN : (N : NT) → Lang N ⊢ (⊕[ t ∈ Tg N ] ty (Cb N t))
unrollN N = ⊕ᴰ-elim (λ t → σ⊕ t ∘⊢ bodyOut N t) ∘⊢ unroll Sys N

rE : Cls → Maybe (Tg E)
rE (after (just ar)) = just arrow
rE (after (just dot)) = just member
rE (headed vid) = just idT
rE _ = nothing

module PE = PushOf BT bracketCover decClsEq rE
module CE = Choice (decTg E) (Cb E)

gE : CE.Guide
gE K .Route.B = PE.PB
gE K .Route.cov = PE.covers
gE K .Route.into arrow =
  PE.atCell (after (just ar)) ∘⊢ bt-open ar
  ∘⊢ (lowerTy ,⊗ (transpAll Q ,⊗ (lowerTy ,⊗ ⊤Ty-intro)))
  ∘⊢ (id⊢ ,⊗ (id⊢ ,⊗ ⊗-assoc)) ∘⊢ (id⊢ ,⊗ ⊗-assoc) ∘⊢ ⊗-assoc
gE K .Route.into member =
  PE.atCell (after (just dot)) ∘⊢ bt-wrap dot
  ∘⊢ (lowerTy ,⊗ (transpAll E ,⊗ (lowerTy ,⊗ (lowerTy ,⊗ ⊤Ty-intro))))
  ∘⊢ (id⊢ ,⊗ (id⊢ ,⊗ (id⊢ ,⊗ ⊗-assoc))) ∘⊢ (id⊢ ,⊗ (id⊢ ,⊗ ⊗-assoc))
  ∘⊢ (id⊢ ,⊗ ⊗-assoc) ∘⊢ ⊗-assoc
gE K .Route.into idT =
  PE.atCell (headed vid) ∘⊢ bt-vid ∘⊢ (lowerTy ,⊗ ⊤Ty-intro)

rQ : Window (more (more none)) → Maybe (Tg Q)
rQ (vid ◂ (rp ◂ _)) = just one
rQ (vid ◂ (cm ◂ _)) = just cons
rQ _ = nothing

module PQ = PushW (more (more none)) rQ
module CQ = Choice (decTg Q) (Cb Q)

gQ : CQ.Guide
gQ K .Route.B = PQ.PB
gQ K .Route.cov = PQ.covers
gQ K .Route.into one =
  PQ.atCell (vid ◂ (rp ◂ ⟨⟩))
  ∘⊢ (lowerTy ,⊗ (lowerTy ,⊗ (liftTy ∘⊢ ⊤Ty-intro))) ∘⊢ ⊗-assoc
gQ K .Route.into cons =
  PQ.atCell (vid ◂ (cm ◂ ⟨⟩))
  ∘⊢ (lowerTy ,⊗ ((lowerTy ,⊗ (liftTy ∘⊢ ⊤Ty-intro)) ∘⊢ ⊗-assoc)) ∘⊢ ⊗-assoc

module F = FixAll LangSet

private
  tokL : {ℓD : Level} {D : TheoryTy ℓD tt} (c : Tok)
    → D ⊢ Parser ⟨▷⟩ ⟨□⟩ (lit↑ c)
  tokL c = mapP liftTy lowerTy ∘⊢ tok c

  altE : (t : Tg E) → ty (▷ F.Pall) ⊢ Parser ⟨□⟩ ⟨□⟩ (Cb E t)
  altE arrow = pmore ∘⊢
    seq (LangSet Q ⊗Set (lit↑ ar ⊗Set LangSet E)) (tokL lp)
      (seq (lit↑ ar ⊗Set LangSet E) (F.callAt Q)
        (seq (LangSet E) (pless ∘⊢ tokL ar) (F.callAt E)))
  altE member = pmore ∘⊢
    seq (LangSet E ⊗Set (lit↑ rp ⊗Set (lit↑ dot ⊗Set lit↑ vid))) (tokL lp)
      (seq (lit↑ rp ⊗Set (lit↑ dot ⊗Set lit↑ vid)) (F.callAt E)
        (seq (lit↑ dot ⊗Set lit↑ vid) (pless ∘⊢ tokL rp)
          (seq (lit↑ vid) (pless ∘⊢ tokL dot) (pless ∘⊢ tokL vid))))
  altE idT = pmore ∘⊢ tokL vid

  altQ : (t : Tg Q) → ty (▷ F.Pall) ⊢ Parser ⟨□⟩ ⟨□⟩ (Cb Q t)
  altQ one = pmore ∘⊢ seq (lit↑ rp) (tokL vid) (pless ∘⊢ tokL rp)
  altQ cons = pmore ∘⊢
    seq (lit↑ cm ⊗Set LangSet Q) (tokL vid)
      (seq (LangSet Q) (pless ∘⊢ tokL cm) (F.callAt Q))

step : ty (▷ F.Pall) ⊢ ty F.Pall
step = &ᴰ-intro λ where
  E → mapP (rollN E) (unrollN E) ∘⊢ CE.choose gE altE
  Q → mapP (rollN Q) (unrollN Q) ∘⊢ CQ.choose gQ altQ

parse : Decidable (Lang E)
parse = F.decideAt step E

L : _
L = Lang E

------------------------------------------------------------------------
-- Accepted

yes-id : L (vid ∷ [])
yes-id = theYes (parse (vid ∷ []) tt) Eq.refl

-- (x) => x
yes-arrow : L (lp ∷ vid ∷ rp ∷ ar ∷ vid ∷ [])
yes-arrow = theYes (parse (lp ∷ vid ∷ rp ∷ ar ∷ vid ∷ []) tt) Eq.refl

-- (x, y) => x
yes-arrow2 : L (lp ∷ vid ∷ cm ∷ vid ∷ rp ∷ ar ∷ vid ∷ [])
yes-arrow2 = theYes (parse (lp ∷ vid ∷ cm ∷ vid ∷ rp ∷ ar ∷ vid ∷ []) tt) Eq.refl

-- (x, y, z) => x
yes-arrow3 : L (lp ∷ vid ∷ cm ∷ vid ∷ cm ∷ vid ∷ rp ∷ ar ∷ vid ∷ [])
yes-arrow3 =
  theYes (parse (lp ∷ vid ∷ cm ∷ vid ∷ cm ∷ vid ∷ rp ∷ ar ∷ vid ∷ []) tt) Eq.refl

-- (x).f
yes-member : L (lp ∷ vid ∷ rp ∷ dot ∷ vid ∷ [])
yes-member = theYes (parse (lp ∷ vid ∷ rp ∷ dot ∷ vid ∷ []) tt) Eq.refl

-- ((x) => x).f  -- the outer `(` is resolved only after matching it
yes-nested : L (lp ∷ lp ∷ vid ∷ rp ∷ ar ∷ vid ∷ rp ∷ dot ∷ vid ∷ [])
yes-nested =
  theYes (parse (lp ∷ lp ∷ vid ∷ rp ∷ ar ∷ vid ∷ rp ∷ dot ∷ vid ∷ []) tt) Eq.refl

-- (x) => (x).f
yes-body : L (lp ∷ vid ∷ rp ∷ ar ∷ lp ∷ vid ∷ rp ∷ dot ∷ vid ∷ [])
yes-body =
  theYes (parse (lp ∷ vid ∷ rp ∷ ar ∷ lp ∷ vid ∷ rp ∷ dot ∷ vid ∷ []) tt) Eq.refl

-- ((x, y) => x).f
yes-deep : L (lp ∷ lp ∷ vid ∷ cm ∷ vid ∷ rp ∷ ar ∷ vid ∷ rp ∷ dot ∷ vid ∷ [])
yes-deep =
  theYes (parse (lp ∷ lp ∷ vid ∷ cm ∷ vid ∷ rp ∷ ar ∷ vid ∷ rp ∷ dot ∷ vid ∷ [])
    tt) Eq.refl

------------------------------------------------------------------------
-- Refuted

no-nil : ¬Ty L []
no-nil = theNo (parse [] tt) Eq.refl

-- (x)  -- a bracket with neither `=>` nor `.f` after it
no-bare : ¬Ty L (lp ∷ vid ∷ rp ∷ [])
no-bare = theNo (parse (lp ∷ vid ∷ rp ∷ []) tt) Eq.refl

-- (x) =>  -- no body
no-nobody : ¬Ty L (lp ∷ vid ∷ rp ∷ ar ∷ [])
no-nobody = theNo (parse (lp ∷ vid ∷ rp ∷ ar ∷ []) tt) Eq.refl

-- (x,) => x  -- trailing comma
no-trailing : ¬Ty L (lp ∷ vid ∷ cm ∷ rp ∷ ar ∷ vid ∷ [])
no-trailing = theNo (parse (lp ∷ vid ∷ cm ∷ rp ∷ ar ∷ vid ∷ []) tt) Eq.refl

-- x.f  -- member access needs the parens
no-unparen : ¬Ty L (vid ∷ dot ∷ vid ∷ [])
no-unparen = theNo (parse (vid ∷ dot ∷ vid ∷ []) tt) Eq.refl

no-close : ¬Ty L (rp ∷ [])
no-close = theNo (parse (rp ∷ []) tt) Eq.refl

-- ((x) => x)  -- matched, but nothing after the match
no-nested-bare : ¬Ty L (lp ∷ lp ∷ vid ∷ rp ∷ ar ∷ vid ∷ rp ∷ [])
no-nested-bare =
  theNo (parse (lp ∷ lp ∷ vid ∷ rp ∷ ar ∷ vid ∷ rp ∷ []) tt) Eq.refl
