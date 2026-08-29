{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Maranget's algorithm, once, for every answer.

   The family is indexed by the width and the model is the clause matrix,
   so `step n` is a `⊢`-term at sort `n` with three rules:

     empty      no rows, so `tfail`, and nothing is consulted
     final      no columns, so `tleaf` at the first row's right-hand side
     switch     recur at `spec o P` for each constructor the head column
                mentions, and at `dflt P` unless it mentions all of them

   NOT ONE PREMISE IS A SUBTERM.  `Unify` had one rule out of four whose
   premise was reached by an operation of the signature -- the trivial
   equation, discharged by `Ans-node`.  Here there are none: `spec o P` and
   `dflt P` rewrite every row of the matrix, and no operation of any
   signature produces either from `P`.  So `Ans-node` never fires,
   `preciseM` is never asked for, and every premise goes through `Ans-re`.
   That is the sharpest statement of what `Ans-re` is for that this
   development has: `Unify` needed it for one rule out of four, and a
   machine whose transition is a global rewrite needs it for all of them.

   `Ans-re` also SUFFICES, and the reason is the one `Core` gives: the maps
   `λ _ → spec o P` and `λ _ → dflt P` are fixed before any answer is
   asked, because the matrix they are computed from is the conclusion's and
   is pinned by the cover cell.  A later premise never reads an earlier
   premise's derivation -- the four premises of a switch are independent,
   and `Ans-&&` conjoins them without any threading at all.

   WHAT THE COVER IS FOR, AND WHAT IT IS NOT.  `matCover` distinguishes
   only "empty" from "headed by row `r`", which is less than the head
   column analysis the algorithm actually branches on.  The head column is
   read by `heads`, a boolean, and it enters the rules as an INDEX of
   `BrSet` -- exactly as `flat1`'s answer indexes `Unify`'s `AuxSet`.  A
   condition that selects between rule shapes rather than constraining one
   is not a side condition and does not belong at `Ans-&&` with a
   `Decidable`; it belongs in the grammar's index, where the answer cannot
   see it at all.

   Nothing below mentions `Dec`, `Maybe` or `ND`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
module Theory.Instances.PatComp.Check where

open import Cubical.Data.Bool using (Bool ; true ; false ; Bool→Type)
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.PatComp.Judgment public


module Check (𝒯 : AnswerFunctor) where

  open Combinators 𝒯 srt order public

  private
    Later : (n : ℕ) → TheoryTy _ n
    Later n = ▷ (AnsFam CompSet) n

  -- One branch of a switch.  The descent proof is a PARAMETER because the
  -- clause that needs it is selected by a boolean the caller computed:
  -- matching `true` does not tell the callee that `heads P o` was `true`,
  -- so the fact travels as `Bool→Type b → _<_` rather than as an equation
  -- the callee would then have to transport along.
  onBr : {n : ℕ} (o : VOp) (P : Mat (suc n)) → Later (suc n) P → (b : Bool)
    → (Bool→Type b → SpecDesc o P)
    → ty (Ans (BrSet n o b P)) P
  onBr o P β false _ = Ans-ofDec P (Sum.inl (tskip , tt))
  onBr {n} o P β true lt = Ans-map {A = Prem} {B = BrSet n o true P}
    carry forget P
    (Ans-re {s = suc n} {s' = VAr o + n} {A = CompSet (VAr o + n)} toSpec P
      (callAt (VAr o + n) (lt tt) β))
    where
    toSpec : Mat (suc n) → Mat (VAr o + n)
    toSpec _ = spec o P

    Prem : TheorySet ℓ-zero (suc n)
    Prem = reSet toSpec (CompSet (VAr o + n))

    carry : ty Prem ⊢ ty (BrSet n o true P)
    carry _ (t , ok) = t , (okNotSkip t ok , ok)

    forget : ty (BrSet n o true P) ⊢ ty Prem
    forget _ (t , (_ , ok)) = t , ok

  -- ...and the default branch, which needs no hypothesis at all: `dflt`
  -- always loses a column, so the guard is discharged by the width even
  -- when the constructor count stands still.
  onDf : {n : ℕ} (P : Mat (suc n)) → Later (suc n) P → (b : Bool)
    → ty (Ans (DfSet n b P)) P
  onDf P β true = Ans-ofDec P (Sum.inl (tskip , tt))
  onDf {n} P β false = Ans-map {A = Prem} {B = DfSet n false P}
    carry forget P
    (Ans-re {s = suc n} {s' = n} {A = CompSet n} toDflt P (callAt n (dfltDesc P) β))
    where
    toDflt : Mat (suc n) → Mat n
    toDflt _ = dflt P

    Prem : TheorySet ℓ-zero (suc n)
    Prem = reSet toDflt (CompSet n)

    carry : ty Prem ⊢ ty (DfSet n false P)
    carry _ (t , ok) = t , (okNotSkip t ok , ok)

    forget : ty (DfSet n false P) ⊢ ty Prem
    forget _ (t , (_ , ok)) = t , ok

  -- The switch rule.  `roll` assembles the tree out of the four premises;
  -- `unroll` takes it apart, and is a match on `Tree` -- an ordinary
  -- datatype -- rather than on the matrix, which is why the three
  -- impossible shapes are refuted by `Ok` reducing to `⊥` and not by
  -- unifying model constructors.
  swAt : {n : ℕ} (r : Row (suc n)) (P : Mat (suc n))
    → Later (suc n) (r ∷ P) → ty (Ans (CompSet (suc n))) (r ∷ P)
  swAt {n} r P β = Ans-map& roll unroll (r ∷ P) (conj , Eq.refl)
    where
    Q : Mat (suc n)
    Q = r ∷ P

    conj : ty (Ans (SwSet n Q)) Q
    conj = Ans-&& Q
      ( onBr vtrueOp Q β (heads Q vtrueOp) (specDesc vtrueOp Q)
      , Ans-&& Q
        ( onBr vfalseOp Q β (heads Q vfalseOp) (specDesc vfalseOp Q)
        , Ans-&& Q
          ( onBr vpairOp Q β (heads Q vpairOp) (specDesc vpairOp Q)
          , onDf Q β (complete Q))))

    roll : ty (SwSet n Q) & ⌈ Q ⌉ ⊢ ty (CompSet (suc n))
    roll m (((a , oa) , (b , ob) , (c , oc) , (d , od)) , Eq.refl) =
      tswitch a b c d , (tt , oa , ob , oc , od)

    unroll : ty (CompSet (suc n)) & ⌈ Q ⌉ ⊢ ty (SwSet n Q)
    unroll m ((tfail , ok) , Eq.refl) = Empty.rec ok
    unroll m ((tskip , ok) , Eq.refl) = Empty.rec ok
    unroll m ((tleaf k , ok) , Eq.refl) = Empty.rec ok
    unroll m ((tswitch a b c d , (_ , oa , ob , oc , od)) , Eq.refl) =
      (a , oa) , (b , ob) , (c , oc) , (d , od)

  branch : (n : ℕ) (y : Maybe (Row n))
    → Later n & Cell n y ⊢ ty (Ans (CompSet n))
  branch n nothing m (β , Eq.refl) = Ans-ofDec [] (Sum.inl (tfail , tt))
  branch zero (just r) m (β , (ms , Eq.refl)) =
    Ans-ofDec (r ∷ ms theRest) (Sum.inl (tleaf (rhsOf r) , refl))
  branch (suc n) (just r) m (β , (ms , Eq.refl)) = swAt r (ms theRest) β

  step : Step CompSet
  step n = look (matCover n) (branch n)

  build : Checker CompSet
  build = fix step


-- The front end.  The derivation IS the tree, so `treeAction` is a
-- projection and there is no compilation step left to get wrong.
open import Theory.Type.SemanticAction.Base MEqns ℕ (λ n → n) mPresentation

import Theory.Combinator.Answer.Decidable
  MEqns ℕ (λ n → n) mPresentation as D
import Theory.Combinator.Answer.Incomplete
  MEqns ℕ (λ n → n) mPresentation as MB
import Theory.Combinator.Answer.NonDet
  MEqns ℕ (λ n → n) mPresentation as NDm

module CD = Check D.DecAnswer
module CM = Check MB.MaybeAnswer
module CN = Check NDm.NDAnswer

treeAction : (n : ℕ) → SemanticAction (Comp n) Tree
treeAction n P d = d .fst , tt

compile : (n : ℕ) → Mat n → Maybe Tree
compile n = observe (CD.build n) (semact-dec (treeAction n))

compileFirst : (n : ℕ) → Mat n → Maybe Tree
compileFirst n = observe (CM.build n) (semact-Maybe (treeAction n))

compileAll : (n : ℕ) → Mat n → List Tree
compileAll n = NDm.observeND (CN.build n) (treeAction n)

-- ...and the count.  `Ok` determines the tree, so anything but one here
-- would say that pattern-match compilation is nondeterministic; `Match`'s
-- `tally` measured a property of the clause LIST, and this one measures a
-- property of the ALGORITHM.
tally : (n : ℕ) → Mat n → ℕ
tally n P = length (compileAll n P)


-- ...and the same run with its correctness attached.  `Agrees n P` is the
-- semantic specification, so `compileV` returns a tree together with the
-- proof that running it is running the matrix.  As in `Unify`, the matrix
-- crosses `observe` with the answer, because `SemanticAction A X` lands in
-- a CONSTANT `X` and a guarantee about the model element cannot travel
-- without it.
open import Theory.Instances.PatComp.Correct public

verifiedAction : (n : ℕ)
  → SemanticAction (Comp n) (Σ[ P ∈ Mat n ] Agrees n P)
verifiedAction n P d = (P , d .fst , sound n (d .fst) P (d .snd)) , tt

compileV : (n : ℕ) (P : Mat n) → Maybe (Σ[ Q ∈ Mat n ] Agrees n Q)
compileV n = observe (CD.build n) (semact-dec (verifiedAction n))
