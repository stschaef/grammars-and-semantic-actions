{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Maranget's algorithm as a `⊢`-term at sort `n` (the width), three rules:

     empty      no rows: `tfail`
     final      no columns: `tleaf` at the first row's right-hand side
     switch     recur at `spec o P` per head constructor, and at `dflt P`
                unless every constructor is mentioned

   No premise is a subterm: all go through `Ans-re`, viable because
   `spec o P`/`dflt P` are pinned by the cover cell before any answer is
   asked.  `heads` enters as an INDEX of `BrSet` -- it selects between
   rule shapes, so it is not an `Ans-&&` side condition. -}
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

  -- the descent proof is a PARAMETER, travelling as `Bool→Type b → _<_`:
  -- an equation would force the callee to transport
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

  -- default branch: `dflt` always loses a column, so the width discharges
  -- the guard
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

  -- `unroll` matches on `Tree`, not the matrix: impossible shapes are
  -- refuted by `Ok` reducing to `⊥`, not by unifying model constructors
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


-- the derivation IS the tree, so `treeAction` is a projection
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

-- `Ok` determines the tree: any count but one would mean nondeterminism
tally : (n : ℕ) → Mat n → ℕ
tally n P = length (compileAll n P)


-- `Agrees n P` is the spec; as in `Unify`, the matrix crosses `observe`
-- with the answer, because `SemanticAction A X` lands in a CONSTANT `X`
open import Theory.Instances.PatComp.Correct public

verifiedAction : (n : ℕ)
  → SemanticAction (Comp n) (Σ[ P ∈ Mat n ] Agrees n P)
verifiedAction n P d = (P , d .fst , sound n (d .fst) P (d .snd)) , tt

compileV : (n : ℕ) (P : Mat n) → Maybe (Σ[ Q ∈ Mat n ] Agrees n Q)
compileV n = observe (CD.build n) (semact-dec (verifiedAction n))
