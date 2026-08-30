{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The discriminating test.

     S → A b | B c        A → a A | a        B → a B | a

   `A` and `B` denote the same language, and which one was meant is settled
   only by the token *after* the a's.  So no bounded lookahead decides at the
   start: this is LL(k) for no k, and SLR(1) -- the reduce/reduce conflict in
   the state `{A → a·, B → a·}` is resolved by FOLLOW(A) = {b}, FOLLOW(B) = {c}.

   `LeftCorner/LeftRec` showed a left-recursive *value* can be rebuilt over a
   left-factored recogniser.  What it did not show is any gain in recognition
   power, because `a (+ a)*` is LL(1).  Here the deferral is genuinely
   unbounded, so if the same recipe works, the recipe is the general one. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.LeftCorner.Defer where

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.Nat using (ℕ) renaming (zero to nzero ; suc to nsuc)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)
import Cubical.Data.Maybe as MB

data Tok : Type where
  ‵a ‵b ‵c : Tok

_≟T_ : (x y : Tok) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
‵a ≟T ‵a = Sum.inl Eq.refl
‵b ≟T ‵b = Sum.inl Eq.refl
‵c ≟T ‵c = Sum.inl Eq.refl
‵a ≟T ‵b = Sum.inr λ ()
‵a ≟T ‵c = Sum.inr λ ()
‵b ≟T ‵a = Sum.inr λ ()
‵b ≟T ‵c = Sum.inr λ ()
‵c ≟T ‵a = Sum.inr λ ()
‵c ≟T ‵b = Sum.inr λ ()

open import Theory.Instances.Monoid.Combinator.Decidable.Base Tok _≟T_ ℓ-zero
open import Theory.Instances.Monoid.Combinator.Syntax Tok _≟T_ DecAnswer
open import Theory.Instances.Monoid.Residual Tok isSetAlphabet
  using (_⊸_ ; ⊸-lam ; ⊸-app ; ⊗ε-unit-r ; ⟦⊗e⟧ ; ⟦⊗e⟧⁻)

-- The two chains.  Same code, but `μ` at *different* arguments, so `Ch false`
-- and `Ch true` are different Agda types: committing to one is a real
-- decision, and it is the decision that cannot be made early.
private
  chBr : Bool → Bool → Functor ℓM Unit (λ _ → tt) tt
  chBr t false = k (literal ‵a)
  chBr t true  = ⊗e _⊙_ (two (k (literal ‵a)) (Var tt))

  ChC : Bool → Unit → Functor ℓM Unit (λ _ → tt) tt
  ChC t _ = ⊕e Bool (chBr t)

  isSetChBr : (t b : Bool) → isSetValued (chBr t b)
  isSetChBr t false = lift (isSetLiteral ‵a)
  isSetChBr t true zero = lift (isSetLiteral ‵a)
  isSetChBr t true (suc zero) = lift tt*

  isSetChC : (t : Bool) (u : Unit) → isSetValued (ChC t u)
  isSetChC t u .fst = lift isSetBool
  isSetChC t u .snd = isSetChBr t

Ch : Bool → TheoryTy _ tt
Ch t = μ (ChC t) tt

oneA : (t : Bool) → literal ‵a ⊢ Ch t
oneA t = roll ∘⊢ σ⊕ false ∘⊢ liftTy

moreA : (t : Bool) → literal ‵a ⊗ Ch t ⊢ Ch t
moreA t = roll ∘⊢ σ⊕ true
  ∘⊢ ⟦⊗e⟧⁻ (k (literal ‵a)) (Var tt) ∘⊢ (liftTy ,⊗ liftTy)

-- S → A b | B c
S : TheoryTy _ tt
S = (Ch false ⊗ literal ‵b) ⊕ (Ch true ⊗ literal ‵c)

-- THE RECOGNISER: the left-factored skeleton `a a* (b | c)`, decided by
-- `Core`'s combinators.  Nothing here commits to `A` or `B`.
BC : TheorySet _ tt
BC = litSet ‵b ⊕Set litSet ‵c

Skel : TheorySet _ tt
Skel = litSet ‵a ⊗Set (StarSet (litSet ‵a) ⊗Set BC)

skel : ⊤Ty ⊢ Parser _ ⟨□⟩ ⟨□⟩ Skel
skel =
  seq (StarSet (litSet ‵a) ⊗Set BC) (pmore ∘⊢ tok ‵a)
    (seq BC (many ℓ-zero (litSet ‵a) (tok ‵a)) (pmore ∘⊢ (tok ‵b <|> tok ‵c)))

decSkel : Decidable (ty Skel)
decSkel = runP _ skel

-- THE ASCENT: build whichever chain the *last* token turned out to demand.
-- `literal a ⊸ Ch t` is again the stack of pending reductions; the fold is
-- run only after the `⊕` has been distributed out, which is the deferral.
chain : (t : Bool) → literal ‵a ⊗ ((literal ‵a) *) ⊢ Ch t
chain t = ⊸-app {A = literal ‵a} {C = Ch t} ∘⊢ (id⊢ ,⊗ go)
  where
  go : ((literal ‵a) *) ⊢ (literal ‵a ⊸ Ch t)
  go = fold*r nil' cons'
    where
    nil' : ⟦ starBranch (literal ‵a) false ⟧TheoryTy (λ _ → literal ‵a ⊸ Ch t)
         ⊢ (literal ‵a ⊸ Ch t)
    nil' = ⊸-lam {A = literal ‵a} {B = εTy} {C = Ch t}
             (oneA t ∘⊢ ⊗ε-unit-r) ∘⊢ NIL-elim {A = literal ‵a}

    cons' : ⟦ starBranch (literal ‵a) true ⟧TheoryTy (λ _ → literal ‵a ⊸ Ch t)
          ⊢ (literal ‵a ⊸ Ch t)
    cons' =
      ⊸-lam {A = literal ‵a} {B = literal ‵a ⊗ (literal ‵a ⊸ Ch t)} {C = Ch t}
        (moreA t ∘⊢ (id⊢ ,⊗ ⊸-app {A = literal ‵a} {C = Ch t}))
      ∘⊢ ((lowerTy ,⊗ lowerTy) ∘⊢ ⟦⊗e⟧ (k (literal ‵a)) (Var tt))

-- distribute the deferred choice out, *then* fold each branch its own way
toS : ty Skel ⊢ S
toS =
  ⊕-elim (inl ∘⊢ (chain false ,⊗ id⊢) ∘⊢ ⊗-assoc⁻)
         (inr ∘⊢ (chain true ,⊗ id⊢) ∘⊢ ⊗-assoc⁻)
  ∘⊢ ⊗⊕-distR ∘⊢ (id⊢ ,⊗ ⊗⊕-distR)

-- ...and the readout, which records *which* nonterminal was built and how
-- long its chain is.
data ST : Type where
  viaA viaB : ℕ → ST

private
  Kn : Unit → TheoryTy ℓ-zero tt
  Kn _ _ = ℕ

  countCh : (t : Bool) → Ch t ⊢ Kn tt
  countCh t = rec (ChC t) alg tt
    where
    alg : (u : Unit) → ⟦ ChC t u ⟧TheoryTy Kn ⊢ Kn u
    alg u = ⊕ᴰ-elim br
      where
      br : (b : Bool) → ⟦ chBr t b ⟧TheoryTy Kn ⊢ Kn tt
      br false m z = 1
      br true m (ms , e , h) = nsuc (h (suc zero) .lower)

  semCh : (t : Bool) → SemanticAction (Ch t) ℕ
  semCh t m ch = countCh t m ch , tt

  semS : SemanticAction S ST
  semS = semact-⊕ (semact-map viaA (semact-⊗₁ (semCh false)))
                  (semact-map viaB (semact-⊗₁ (semCh true)))

parseS : String → MB.Maybe ST
parseS = observe decSkel (semact-dec (semact-map-g toS semS))

-- The decisive cases: five `a`s go by before the token that says which
-- nonterminal it was, so no bounded lookahead could have committed at the
-- start -- and the right chain still comes out.
deferred : passes
  (parseS at
    ( (‵a ∷ ‵b ∷ [])                               ↦ MB.just (viaA 1)
    ∷ (‵a ∷ ‵a ∷ ‵a ∷ ‵b ∷ [])                     ↦ MB.just (viaA 3)
    ∷ (‵a ∷ ‵c ∷ [])                               ↦ MB.just (viaB 1)
    ∷ (‵a ∷ ‵a ∷ ‵a ∷ ‵a ∷ ‵a ∷ ‵c ∷ [])           ↦ MB.just (viaB 5)
    ∷ [] ))
deferred = refl

rejected : passes
  (parseS at
    ( []                          ↦ MB.nothing
    ∷ (‵b ∷ [])                   ↦ MB.nothing
    ∷ (‵a ∷ [])                   ↦ MB.nothing
    ∷ (‵a ∷ ‵a ∷ [])              ↦ MB.nothing
    ∷ (‵a ∷ ‵b ∷ ‵c ∷ [])         ↦ MB.nothing
    ∷ (‵b ∷ ‵a ∷ [])              ↦ MB.nothing
    ∷ [] ))
rejected = refl
