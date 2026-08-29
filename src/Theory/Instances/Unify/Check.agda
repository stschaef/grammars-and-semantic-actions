{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- First-order unification, once, for every answer.

   The family is indexed by the scope and the model is the equation stack,
   so `step n` is a `⊢`-term at sort `n` with three rules:

     empty      `Sol n []` holds, and nothing is consulted
     clash      `flat1` failed, so the grammar is empty and is refuted
     trivial    `flat1` produced no equation: recur on the *slot*
     flexible   `flat1` produced `x ≟ u`: check the occurs condition and
                recur at scope `n-1` on the substituted stack

   Only the trivial rule's premise is a subterm of the conclusion, and it
   is the only one built by `Ans-node`.  The flexible rule's premise sits
   at a stack that no operation produces from the conclusion's -- it is the
   *result* of applying a substitution -- and that is what `Ans-re` is for:
   an answer at `f m` for `A` is an answer at `m` for `A ∘ f`.  Nothing
   here is a bind: `f` is fixed before any answer is asked, so a premise
   still cannot read another premise's derivation.  That distinction is the
   whole content of the file; see this module's report in `Core`.

   Nothing below mentions `Dec`, `Maybe` or `ND`, and the three grammars
   `AuxSet`/`FlexSet`/`ChkSet` are the judgment's own unfoldings -- each is
   definitionally the previous one, so every `Ans-map&` here is the
   identity under the cover cell's hypothesis, EXCEPT at the flexible rule.
   There the judgment carries the checked term, so the premise is the
   conclusion minus one assignment; `carry`/`forget` in `onChk` are that
   one assignment, and they are the entire price of making the derivation
   be the substitution.

   `Ans-map&`'s second map is the reason this file stops where it does.
   The judgment says the MACHINE succeeds; the specification would say a
   unifier EXISTS, and `Correct` gets from the first to the second.  It
   does not get back, and it cannot: `forget` would then have to turn "some
   `AList (suc n)` unifies `p ∷ ps`" into "some `AList n` unifies the
   substituted stack", and an `AList` is a chain of scope-dropping
   assignments, not an arbitrary substitution -- the restriction of a chain
   along `thin x` need not be a chain (at `n = m = 1`, `AList 1` targeting
   `1` is the identity alone, while the restriction can be
   `fork (var 0) (var 0)`).  The only way to produce the premise's chain is
   to run the algorithm, which is what the answer we are trying to build
   would have done.  See the end of `Correct`. -}
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

-- The judgment, and the three grammars it unfolds through.  Each is the
-- previous one with one more thing decided, and all of them are constant
-- in the model element -- the equation stack is fixed by the cover cell,
-- and what is left to say about it is a closed proposition.
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

  -- The occurs check, and the recursive call it licenses.  `Ans-re` moves
  -- the answer from the stack the substitution produced back to the stack
  -- the conclusion is about; the scope has dropped, so the two are not
  -- even at the same sort.
  --
  -- The premise is now one `Ans-map&` away from the conclusion rather than
  -- definitionally it, and that map is the whole cost of proof-relevance:
  -- `carry` pairs the checked term with the sub-derivation and `forget`
  -- drops it again.  `forget` is a `subst` and not a projection because the
  -- conclusion quantifies over the assignment, and the premise is about the
  -- one `check` actually returned; `checked` is what identifies them.
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

  -- ...and at scope zero there is no unknown to be flexible about.
  onFlex : {n : ℕ} (x : Fin n) (u : Tm n) (qs : FStack n)
    (p : Prob n) (ps : Stack n) → Later n (p ∷ ps)
    → ty (Ans (FlexSet n x u qs ps)) (p ∷ ps)
  onFlex {suc n} x u qs p ps β = onChk x u qs p ps β (check x u)

  -- The three rules for a nonempty stack, indexed by what `flat1` made of
  -- its head equation.  The checker never matches on a term.
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


-- The front end.  The derivation IS the substitution now, so `mguAction`
-- is a projection: `mgu` reads each assignment off the derivation that
-- recorded it, and no clause of it calls `check`.
--
-- This lives in the client, not in the tests: a client exports its front
-- end and a test calls it.
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


-- ...and the same run with its correctness attached.  `Unifier n` is a
-- GRAMMAR -- a substitution together with the proof that it unifies the
-- stack -- so the readout is a `⊢`-term into it, and `verifiedTm` says so.
--
-- Externalising is the awkward step, and the awkwardness is the
-- framework's and not the client's: `SemanticAction A X` lands in a
-- CONSTANT `X`, so a guarantee about the model element cannot cross
-- `observe` unless the element crosses with it.  Hence the `Σ`: `observe`
-- applies the action at exactly the element it was asked about, so
-- `solveV n ps` computes to `just (ps , σ , pf)` and `pf` typechecks at
-- `ps` on the nose.
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
