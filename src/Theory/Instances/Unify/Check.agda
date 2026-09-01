{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- First-order unification, once, for every answer.
     empty      `Sol n []` holds
     clash      `flat1` failed: refuted
     trivial    `flat1` produced no equation: recur on the slot
     flexible   `x ≟ u`: occurs-check, recur at scope `n-1` (via `Ans-re`)
   Not the specification rule by rule: restricting a chain along `thin x`
   need not be a chain (`AList 1` targeting `1` is the identity alone; the
   restriction can be `fork (var 0) (var 0)`).  They agree extensionally:
   `Solvable`'s `complete`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
module Theory.Instances.Unify.Check where

open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Unify.Guard public

SolSet : (n : ℕ) → TheorySet ℓ-zero n
SolSet n = Sol n , isSetSol n

AuxSet : (n : ℕ) (fl : Maybe (FStack n)) (ps : Stack n) → TheorySet ℓ-zero n
AuxSet n fl ps = (λ _ → onFlat n fl ps)
               , λ _ → isProp→isSet (isPropOnFlat n fl ps)

FlexSet : (n : ℕ) (x : Fin n) (u : Tm n) (qs : FStack n) (ps : Stack n)
        → TheorySet ℓ-zero n
FlexSet n x u qs ps = (λ _ → flexAt n x u qs ps)
                    , λ _ → isProp→isSet (isPropFlexAt n x u qs ps)

ChkSet : (n : ℕ) (x : Fin (suc n)) (u : Tm (suc n)) (qs : FStack (suc n))
  (ps : Stack (suc n)) (c : Maybe (Tm n)) → TheorySet ℓ-zero (suc n)
ChkSet n x u qs ps c = (λ _ → onCheck n x u qs ps c)
                     , λ _ → isProp→isSet (isPropOnCheck n x u qs ps c)


module Check (𝒯 : AnswerFunctor) where

  open Combinators 𝒯 srt order public

  private
    Later : (n : ℕ) → TheoryTy _ n
    Later n = ▷ (AnsFam SolSet) n

-- `forget` is a `subst`, not a projection: the conclusion quantifies over
-- the assignment, the premise is about the one `check` returned.
  onChk : {n : ℕ} (x : Fin (suc n)) (u : Tm (suc n)) (qs : FStack (suc n))
    (p : Prob (suc n)) (ps : Stack (suc n)) → Later (suc n) (p ∷ ps)
    → (c : Maybe (Tm n)) → ty (Ans (ChkSet n x u qs ps c)) (p ∷ ps)
  onChk x u qs p ps β nothing =
    Ans-ofDec (p ∷ ps) (Sum.inr λ z → Empty.rec (z .snd .fst))
  onChk {n} x u qs p ps β (just w) =
    Ans-map& {A = Prem} {B = ChkSet n x u qs ps (just w)} carry forget
      (p ∷ ps)
      (Ans-re {A = SolSet n} toNext (p ∷ ps) (callAt n scopeStep β) , Eq.refl)
    where
    next : Stack n
    next = applyStack x w (unflexAll qs ++ ps)

    toNext : Stack (suc n) → Stack n
    toNext _ = next

    Prem : TheorySet ℓ-zero (suc n)
    Prem = reSet toNext (SolSet n)

    carry : ty Prem & ⌈ p ∷ ps ⌉ ⊢ ty (ChkSet n x u qs ps (just w))
    carry m (d , Eq.refl) = assign w refl d

    forget : ty (ChkSet n x u qs ps (just w)) & ⌈ p ∷ ps ⌉ ⊢ ty Prem
    forget m (assign w' e d , Eq.refl) =
      subst (λ v → Sol n (applyStack x v (unflexAll qs ++ ps))) (sym e) d

  -- At scope zero there is no unknown to be flexible about.
  onFlex : {n : ℕ} (x : Fin n) (u : Tm n) (qs : FStack n)
    (p : Prob n) (ps : Stack n) → Later n (p ∷ ps)
    → ty (Ans (FlexSet n x u qs ps)) (p ∷ ps)
  onFlex {suc n} x u qs p ps β = onChk x u qs p ps β (check x u)

  -- The checker never matches on a term.
  onFl : {n : ℕ} (p : Prob n) (ps : Stack n) → Later n (p ∷ ps)
    → (fl : Maybe (FStack n)) → ty (Ans (AuxSet n fl ps)) (p ∷ ps)
  onFl p ps β nothing = Ans-ofDec (p ∷ ps) (Sum.inr λ ())
  onFl {n} p ps β (just []) =
    Ans-map& roll unroll (p ∷ ps) (nodeAns , Eq.refl)
    where
    As : NodeArgs ℓ-zero (n , p)
    As _ _ = SolSet n

    nodeAns : ty (Ans (⊗ᴰSet (n , p) As)) (p ∷ ps)
    nodeAns = Ans-node (n , p) (preciseU (n , p)) {As = As} {ms = λ _ → ps}
      λ _ → callAt n tailStep β

    roll : ⊗ᴰ (n , p) As & ⌈ p ∷ ps ⌉ ⊢ ty (AuxSet n (just []) ps)
    roll m' (t , Eq.refl) =
      node-elim {C = λ z → Sol n (tailOf ps z)} (λ ws → ws theRest) (p ∷ ps) t

    unroll : ty (AuxSet n (just []) ps) & ⌈ p ∷ ps ⌉ ⊢ ⊗ᴰ (n , p) As
    unroll m' (a , Eq.refl) = node-mk {ms = λ _ → ps} λ _ → a
  onFl p ps β (just (e ∷ qs)) = onFlex (e .fst) (e .snd) qs p ps β

  step : Step SolSet
  step n = look (stackCover n) branch
    where
    branch : (y : Maybe (Prob n))
      → Later n & Cell n y ⊢ ty (Ans (SolSet n))
    branch nothing m (β , Eq.refl) = Ans-ofDec [] (Sum.inl tt)
    branch (just p) m (β , (ms , Eq.refl)) =
      Ans-map& fwd bwd (p ∷ ms theRest) (onFl p (ms theRest) β (flat1 p) , Eq.refl)
      where
      fwd : ty (AuxSet n (flat1 p) (ms theRest)) & ⌈ p ∷ ms theRest ⌉ ⊢ Sol n
      fwd m' (a , Eq.refl) = a

      bwd : Sol n & ⌈ p ∷ ms theRest ⌉ ⊢ ty (AuxSet n (flat1 p) (ms theRest))
      bwd m' (a , Eq.refl) = a

  unify : Checker SolSet
  unify = fix step


-- The derivation IS the substitution: `mgu` never calls `check`.
open import Theory.Type.SemanticAction.Base UEqns ℕ (λ n → n) uPresentation

import Theory.Combinator.Answer.Decidable
  UEqns ℕ (λ n → n) uPresentation as D

module CD = Check D.DecAnswer

mguAction : (n : ℕ) → SemanticAction (Sol n) (AList n)
mguAction n ps d = mgu n ps d , tt

solve : (n : ℕ) → Stack n → Maybe (AList n)
solve n = observe (CD.unify n) (semact-dec (mguAction n))

unifyTm : (n : ℕ) → Tm n → Tm n → Maybe (AList n)
unifyTm n t u = solve n ((t , u) ∷ [])


-- `SemanticAction A X` lands in a constant `X`, so the correctness proof
-- can only cross `observe` paired with its stack: hence the `Σ`.
open import Theory.Instances.Unify.Correct public

verifiedTm : (n : ℕ) → Sol n ⊢ Unifier n
verifiedTm = verified

verifiedAction : (n : ℕ)
  → SemanticAction (Sol n) (Σ[ ps ∈ Stack n ] Unifier n ps)
verifiedAction n ps d = (ps , verifiedTm n ps d) , tt

solveV : (n : ℕ) → (ps : Stack n) → Maybe (Σ[ qs ∈ Stack n ] Unifier n qs)
solveV n = observe (CD.unify n) (semact-dec (verifiedAction n))

unifierTm : (n : ℕ) → Tm n → Tm n → Maybe (Σ[ qs ∈ Stack n ] Unifier n qs)
unifierTm n t u = solveV n ((t , u) ∷ [])
