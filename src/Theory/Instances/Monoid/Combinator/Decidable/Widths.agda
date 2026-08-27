{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A grammar family that needs exactly `k` tokens of lookahead.

     S ::= aᵏ⁺¹ S b | aᵏ⁺¹ c

   Both productions lead with the same `k+1` letters, so no width below
   `k+2` separates them; at `k+2` the cover does.  Everything below is
   indexed by the width, so nothing here is an LL(2) development that
   happens to be written twice -- `Route`, `routeIn`, `choose` and the
   fixpoint are the same terms as at width one. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Decidable.Widths where

open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)

data Tok : Type where
  ta tb tc : Tok

_≟T_ : (x y : Tok) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
ta ≟T ta = Sum.inl Eq.refl
tb ≟T tb = Sum.inl Eq.refl
tc ≟T tc = Sum.inl Eq.refl
ta ≟T tb = Sum.inr λ () ; ta ≟T tc = Sum.inr λ ()
tb ≟T ta = Sum.inr λ () ; tb ≟T tc = Sum.inr λ ()
tc ≟T ta = Sum.inr λ () ; tc ≟T tb = Sum.inr λ ()

open import Theory.Instances.Monoid.Combinator.Decidable.Window Tok _≟T_ (ℓ-suc ℓ-zero)
open import Theory.Instances.Monoid.Residual Tok isSetAlphabet
  using (⟦⊗e⟧ ; ⟦⊗e⟧⁻)

-- The two lookahead windows, at width `k+2`.

aFill : (n : Width) → Window n
aFill none = ⟨⟩
aFill (more n) = ta ◂ aFill n

aThenC : (n : Width) → Window (more n)
aThenC none = tc ◂ ⟨⟩
aThenC (more n) = ta ◂ aThenC n

-- The grammar, indexed by the width

data NT : Type ℓ-zero where
  St : NT

data Tg : NT → Type ℓ-zero where
  nest flat : Tg St

decTg : (N : NT) → DiscreteEq (Tg N)
decTg St nest nest = Sum.inl Eq.refl
decTg St flat flat = Sum.inl Eq.refl
decTg St nest flat = Sum.inr λ ()
decTg St flat nest = Sum.inr λ ()

Code : Type _
Code = Functor ℓM NT (λ _ → tt) tt

infixr 20 _⊗c_
_⊗c_ : Code → Code → Code
F ⊗c G = ⊗e _⊙_ (two F G)

-- `n` copies of `a`, right-nested so the body matches `Λw`'s shape
pow : Width → Code → Code
pow none F = F
pow (more n) F = k (literal ta) ⊗c pow n F

-- The routing.  Read `a`s down the window; the last letter decides.
-- Structural in the width, so it computes at every `k`.

rt : (n : Width) → Window (more (more n)) → Maybe (Tg St)
rt none ⟨⟩ = nothing
rt none (ta ◂ ⟨⟩) = nothing
rt none (tb ◂ _) = nothing
rt none (tc ◂ _) = nothing
rt none (ta ◂ (ta ◂ _)) = just nest
rt none (ta ◂ (tb ◂ _)) = nothing
rt none (ta ◂ (tc ◂ _)) = just flat
rt (more n) ⟨⟩ = nothing
rt (more n) (ta ◂ w) = rt n w
rt (more n) (tb ◂ _) = nothing
rt (more n) (tc ◂ _) = nothing

rt-nest : (n : Width) → rt n (aFill (more (more n))) Eq.≡ just nest
rt-nest none = Eq.refl
rt-nest (more n) = rt-nest n

rt-flat : (n : Width) → rt n (aThenC (more n)) Eq.≡ just flat
rt-flat none = Eq.refl
rt-flat (more n) = rt-flat n

module Gram (kk : Width) where

  body : (N : NT) → Tg N → Code
  body St nest = pow (more kk) (Var St ⊗c k (literal tb))
  body St flat = pow (more kk) (k (literal tc))

  Sys : (N : NT) → Code
  Sys N = ⊕e (Tg N) (body N)

  isSetPow : (n : Width) (F : Code) → isSetValued F → isSetValued (pow n F)
  isSetPow none F sF = sF
  isSetPow (more n) F sF = λ where
    zero → lift (isSetLiteral ta)
    (suc zero) → isSetPow n F sF

  isSetSys : (N : NT) → isSetValued (Sys N)
  isSetSys St = lift isSetTg , λ where
      nest → isSetPow (more kk) _ λ where
        zero → lift tt*
        (suc zero) → lift (isSetLiteral tb)
      flat → isSetPow (more kk) _ (lift (isSetLiteral tc))
    where
    isSetTg : isSet (Tg St)
    isSetTg = Discrete→isSet λ t u → Sum.rec
      (λ p → yes (Eq.eqToPath p)) (λ ¬p → no λ p → ¬p (Eq.pathToEq p))
      (decTg St t u)
      where open import Cubical.Relation.Nullary.Base using (yes ; no)
            open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)

  Lang : NT → TheoryTy _ tt
  Lang = μ Sys

  LangSet : NT → TheorySet ℓG tt
  LangSet N = Lang N , isSetμ Sys isSetSys N

  -- Bodies, and the one unrolling.  Both are inductions on the width.

  lit↑ : Tok → TheorySet ℓG tt
  lit↑ c = LiftTheoryTy ℓG (literal c) , isSetLiftTheoryTy (isSetLiteral c)

  CbPow : Width → TheorySet ℓG tt → TheorySet ℓG tt
  CbPow none X = X
  CbPow (more n) X = lit↑ ta ⊗Set CbPow n X

  Cb : (N : NT) → Tg N → TheorySet ℓG tt
  Cb St nest = CbPow (more kk) (LangSet St ⊗Set lit↑ tb)
  Cb St flat = CbPow (more kk) (lit↑ tc)

  powIn : (n : Width) {F : Code} {X : TheorySet ℓG tt}
    → ty X ⊢ ⟦ F ⟧TheoryTy Lang
    → ty (CbPow n X) ⊢ ⟦ pow n F ⟧TheoryTy Lang
  powIn none f = f
  powIn (more n) {F} f = ⟦⊗e⟧⁻ _ _ ∘⊢ ((liftTy ∘⊢ lowerTy) ,⊗ powIn n {F} f)

  powOut : (n : Width) {F : Code} {X : TheorySet ℓG tt}
    → ⟦ F ⟧TheoryTy Lang ⊢ ty X
    → ⟦ pow n F ⟧TheoryTy Lang ⊢ ty (CbPow n X)
  powOut none f = f
  powOut (more n) {F} f =
    ((liftTy ∘⊢ lowerTy) ,⊗ powOut n {F} f) ∘⊢ ⟦⊗e⟧ _ _

  bodyIn : (N : NT) (t : Tg N) → ty (Cb N t) ⊢ ⟦ body N t ⟧TheoryTy Lang
  bodyIn St nest =
    powIn (more kk) (⟦⊗e⟧⁻ _ _ ∘⊢ (liftTy ,⊗ (liftTy ∘⊢ lowerTy)))
  bodyIn St flat = powIn (more kk) (liftTy ∘⊢ lowerTy)

  bodyOut : (N : NT) (t : Tg N) → ⟦ body N t ⟧TheoryTy Lang ⊢ ty (Cb N t)
  bodyOut St nest =
    powOut (more kk) ((lowerTy ,⊗ (liftTy ∘⊢ lowerTy)) ∘⊢ ⟦⊗e⟧ _ _)
  bodyOut St flat = powOut (more kk) (liftTy ∘⊢ lowerTy)

  rollN : (N : NT) → (⊕[ t ∈ Tg N ] ty (Cb N t)) ⊢ Lang N
  rollN N = roll ∘⊢ ⊕ᴰ-elim λ t → σ⊕ t ∘⊢ bodyIn N t

  unrollN : (N : NT) → Lang N ⊢ (⊕[ t ∈ Tg N ] ty (Cb N t))
  unrollN N = ⊕ᴰ-elim (λ t → σ⊕ t ∘⊢ bodyOut N t) ∘⊢ unroll Sys N

  -- What each production leads with, at width `k+2`.

  -- every body begins with `a`, which is one unrolling
  firstS : Lang St ⊢ literal ta ⊗ ⊤Ty
  firstS = ⊕ᴰ-elim br ∘⊢ unroll Sys St
    where
    br : (t : Tg St) → ⟦ body St t ⟧TheoryTy Lang ⊢ literal ta ⊗ ⊤Ty
    br nest = (lowerTy ,⊗ ⊤Ty-intro)
      ∘⊢ ⟦⊗e⟧ (k (literal ta)) (pow kk (Var St ⊗c k (literal tb)))
    br flat = (lowerTy ,⊗ ⊤Ty-intro)
      ∘⊢ ⟦⊗e⟧ (k (literal ta)) (pow kk (k (literal tc)))

  leadFlat : (n : Width) → ty (CbPow n (lit↑ tc)) ⊗ ⊤Ty ⊢ Λw (aThenC n)
  leadFlat none = lowerTy ,⊗ (liftTy ∘⊢ ⊤Ty-intro)
  leadFlat (more n) = (lowerTy ,⊗ leadFlat n) ∘⊢ ⊗-assoc

  leadNest : (n : Width)
    → ty (CbPow n (LangSet St ⊗Set lit↑ tb)) ⊗ ⊤Ty ⊢ Λw (aFill (more n))
  leadNest none =
    (id⊢ ,⊗ (liftTy ∘⊢ ⊤Ty-intro)) ∘⊢ ⊗-assoc
    ∘⊢ (firstS ,⊗ id⊢) ∘⊢ (id⊢ ,⊗ ⊤Ty-intro) ∘⊢ ⊗-assoc
  leadNest (more n) = (lowerTy ,⊗ leadNest n) ∘⊢ ⊗-assoc

  -- The route, at width `k+2`, and the parser.

  module PW = PushW (more (more kk)) (rt kk)
  module CS = Choice (decTg St) (Cb St)

  gS : CS.Guide
  gS K .Route.B = PW.PB
  gS K .Route.cov = PW.covers
  gS K .Route.into nest =
    Eq.transport (λ v → ty (Cb St nest) ⊗ ty K ⊢ PW.PB v) (rt-nest kk)
      (PW.atCell (aFill (more (more kk)))
       ∘⊢ leadNest (more kk) ∘⊢ (id⊢ ,⊗ ⊤Ty-intro))
  gS K .Route.into flat =
    Eq.transport (λ v → ty (Cb St flat) ⊗ ty K ⊢ PW.PB v) (rt-flat kk)
      (PW.atCell (aThenC (more kk))
       ∘⊢ leadFlat (more kk) ∘⊢ (id⊢ ,⊗ ⊤Ty-intro))

  module F = FixAll ℓG LangSet

  private
    tokL : {ℓD : Level} {D : TheoryTy ℓD tt} (c : Tok)
      → D ⊢ Parser ℓG ⟨▷⟩ ⟨□⟩ (lit↑ c)
    tokL c = mapP liftTy lowerTy ∘⊢ tok c

    -- `k+1` tokens, then the rest: one `seq` per `a`, by induction
    powP : {ℓD : Level} {D : TheoryTy ℓD tt} (n : Width) {X : TheorySet ℓG tt}
      → D ⊢ Parser ℓG ⟨▷⟩ ⟨▷⟩ X → D ⊢ Parser ℓG ⟨▷⟩ ⟨□⟩ (CbPow (more n) X)
    powP none {X} p = seq X (tokL ta) p
    powP (more n) {X} p = seq (CbPow (more n) X) (tokL ta) (pless ∘⊢ powP n p)

    altS : (t : Tg St) → ty (▷ F.Pall) ⊢ Parser ℓG ⟨□⟩ ⟨□⟩ (Cb St t)
    altS nest = pmore ∘⊢ powP kk
      (seq (lit↑ tb) (F.callAt St) (pless ∘⊢ tokL tb))
    altS flat = pmore ∘⊢ powP kk (pless ∘⊢ tokL tc)

  step : ty (▷ F.Pall) ⊢ ty F.Pall
  step = &ᴰ-intro λ where
    St → mapP (rollN St) (unrollN St) ∘⊢ CS.choose gS altS

  parse : Decidable (Lang St)
  parse = F.decideAt step St
