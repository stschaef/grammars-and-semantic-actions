{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
-- Arithmetic expressions
-- TODO this should be LL(1). Talk about the "Route" used
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Decidable.Arith where

open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)

------------------------------------------------------------------------
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

open import Theory.Instances.Monoid.Combinator.Decidable.Routed Tok _≟T_ (ℓ-suc ℓ-zero)
open import Theory.Instances.Monoid.Residual Tok isSetAlphabet
  using (⟦⊗e⟧ ; ⟦⊗e⟧⁻)

------------------------------------------------------------------------
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
Cb Exp' done   = ε↑Set
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

rExp : M₁ → Maybe (Tag Exp)
rExp (tk nm) = just enum
rExp (tk lb) = just eparen
rExp _ = nothing

module CE = Choice (decTag Exp) (Cb Exp)

gExp : CE.Guide
gExp K .Route.B = Push.PB rExp
gExp K .Route.cov = Push.covers rExp
gExp K .Route.into enum =
  Push.atCell rExp (tk nm) ∘⊢ (lowerTy ,⊗ ⊤Ty-intro) ∘⊢ ⊗-assoc
gExp K .Route.into eparen =
  Push.atCell rExp (tk lb) ∘⊢ (lowerTy ,⊗ ⊤Ty-intro)
  ∘⊢ ⊗-assoc ∘⊢ ⊗-assoc ∘⊢ ⊗-assoc

module F = FixAll LangSet

private
  tokL : {ℓD : Level} {D : TheoryTy ℓD tt} (c : Tok)
    → D ⊢ Parser ⟨▷⟩ ⟨□⟩ (lit↑ c)
  tokL c = mapP liftTy lowerTy ∘⊢ tok c

  altExp : (t : Tag Exp) → ty (▷ F.Pall) ⊢ Parser ⟨□⟩ ⟨□⟩ (Cb Exp t)
  altExp enum = pmore ∘⊢ seq (LangSet Exp') (tokL nm) (F.callAt Exp')
  altExp eparen = pmore ∘⊢ seq (LangSet Exp') inner (F.callAt Exp')
    where
    inner : ty (▷ F.Pall)
      ⊢ Parser ⟨▷⟩ ⟨□⟩ ((lit↑ lb ⊗Set LangSet Exp) ⊗Set lit↑ rb)
    inner = seq (lit↑ rb)
              (seq (LangSet Exp) (tokL lb) (F.callAt Exp))
              (pless ∘⊢ tokL rb)

  expP : ty (▷ F.Pall) ⊢ Parser ⟨□⟩ ⟨□⟩ (LangSet Exp)
  expP = mapP (rollN Exp) (unrollN Exp) ∘⊢ CE.choose gExp altExp

  exp'P : ty (▷ F.Pall) ⊢ Parser ⟨□⟩ ⟨□⟩ (LangSet Exp')
  exp'P = mapP rollE' unrollE' ∘⊢ (addP <|> doneP)
    where
    addP : ty (▷ F.Pall) ⊢ Parser ⟨□⟩ ⟨□⟩ (Cb Exp' add)
    addP = pmore ∘⊢ seq (LangSet Exp) (tokL pl) (F.callAt Exp)

    doneP : ty (▷ F.Pall) ⊢ Parser ⟨□⟩ ⟨□⟩ (Cb Exp' done)
    doneP = mapP liftTy lowerTy ∘⊢ nil

    rollE' : ty (Cb Exp' add) ⊕ ty (Cb Exp' done) ⊢ Lang Exp'
    rollE' = rollN Exp' ∘⊢ ⊕-elim (σ⊕ add) (σ⊕ done)

    unrollE' : Lang Exp' ⊢ ty (Cb Exp' add) ⊕ ty (Cb Exp' done)
    unrollE' = ⊕ᴰ-elim (λ where done → inr ; add → inl) ∘⊢ unrollN Exp'

step : ty (▷ F.Pall) ⊢ ty F.Pall
step = &ᴰ-intro λ where
  Exp  → expP
  Exp' → exp'P

decide : (N : NT) → Decidable (Lang N)
decide = F.decideAt step

parse : Decidable (Lang Exp)
parse = decide Exp

E : _
E = Lang Exp

yes-n : E (nm ∷ [])
yes-n = theYes (parse (nm ∷ []) tt) Eq.refl

yes-add : E (nm ∷ pl ∷ nm ∷ [])
yes-add = theYes (parse (nm ∷ pl ∷ nm ∷ []) tt) Eq.refl

yes-add3 : E (nm ∷ pl ∷ nm ∷ pl ∷ nm ∷ [])
yes-add3 = theYes (parse (nm ∷ pl ∷ nm ∷ pl ∷ nm ∷ []) tt) Eq.refl

yes-paren : E (lb ∷ nm ∷ rb ∷ [])
yes-paren = theYes (parse (lb ∷ nm ∷ rb ∷ []) tt) Eq.refl

yes-paren-add : E (lb ∷ nm ∷ pl ∷ nm ∷ rb ∷ [])
yes-paren-add = theYes (parse (lb ∷ nm ∷ pl ∷ nm ∷ rb ∷ []) tt) Eq.refl

yes-mixed : E (lb ∷ nm ∷ pl ∷ nm ∷ rb ∷ pl ∷ nm ∷ [])
yes-mixed = theYes (parse (lb ∷ nm ∷ pl ∷ nm ∷ rb ∷ pl ∷ nm ∷ []) tt) Eq.refl

yes-nest : E (lb ∷ lb ∷ nm ∷ rb ∷ rb ∷ [])
yes-nest = theYes (parse (lb ∷ lb ∷ nm ∷ rb ∷ rb ∷ []) tt) Eq.refl

------------------------------------------------------------------------
-- Rejected: each `no` is a refutation, not an absence.

no-nil : ¬Ty E []
no-nil = theNo (parse [] tt) Eq.refl

no-plus : ¬Ty E (pl ∷ [])
no-plus = theNo (parse (pl ∷ []) tt) Eq.refl

no-trailing : ¬Ty E (nm ∷ pl ∷ [])
no-trailing = theNo (parse (nm ∷ pl ∷ []) tt) Eq.refl

no-unclosed : ¬Ty E (lb ∷ nm ∷ [])
no-unclosed = theNo (parse (lb ∷ nm ∷ []) tt) Eq.refl

no-extra-close : ¬Ty E (lb ∷ nm ∷ rb ∷ rb ∷ [])
no-extra-close = theNo (parse (lb ∷ nm ∷ rb ∷ rb ∷ []) tt) Eq.refl

no-juxtapose : ¬Ty E (nm ∷ nm ∷ [])
no-juxtapose = theNo (parse (nm ∷ nm ∷ []) tt) Eq.refl

no-empty-parens : ¬Ty E (lb ∷ rb ∷ [])
no-empty-parens = theNo (parse (lb ∷ rb ∷ []) tt) Eq.refl

------------------------------------------------------------------------
-- Scale.  `chain k` is `n + n + … + n` with k additions; `nest d` is
-- `[[…[n]…]]` at depth d.

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.List using (List ; _++_)

chain : ℕ → List Tok
chain zero = nm ∷ []
chain (suc j) = nm ∷ pl ∷ chain j

nest : ℕ → List Tok
nest zero = nm ∷ []
nest (suc e) = lb ∷ (nest e ++ (rb ∷ []))

yes-chain8 : E (chain 8)
yes-chain8 = theYes (parse (chain 8) tt) Eq.refl

yes-chain32 : E (chain 32)
yes-chain32 = theYes (parse (chain 32) tt) Eq.refl

yes-nest8 : E (nest 8)
yes-nest8 = theYes (parse (nest 8) tt) Eq.refl

yes-nest32 : E (nest 32)
yes-nest32 = theYes (parse (nest 32) tt) Eq.refl

no-nest32 : ¬Ty E (lb ∷ nest 32)
no-nest32 = theNo (parse (lb ∷ nest 32) tt) Eq.refl
