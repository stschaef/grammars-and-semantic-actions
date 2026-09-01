{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Decision trees; `Comp n P = Σ[ t ∈ Tree ] Ok n t P`.  `Ok` recurses on
   the TREE, not on `runTree t vs ≡ matrixRun P vs`: `Ans-map&` needs a map
   back to the premises' grammars, which the semantic spec is too weak to
   invert.  `tskip` is Maranget's absent branch. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.PatComp.Judgment where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Empty using (⊥ ; isProp⊥)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; isSetℕ)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Sum using (_⊎_ ; isSet⊎)
import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit using (Unit ; tt ; isPropUnit)
open import Cubical.Data.W.Indexed using (IW ; node ; isOfHLevelSuc-IW)

open import Theory.Instances.PatComp.Guard public

private variable n : ℕ

-- One switch slot per `Val` constructor plus the default; `tskip` marks a
-- constructor the head column does not mention.
data Tree : Type ℓ-zero where
  tfail tskip : Tree
  tleaf : ℕ → Tree
  tswitch : Tree → Tree → Tree → Tree → Tree

onTrue onFalse onPair otherwise : Tree → Tree
onTrue (tswitch a _ _ _) = a
onTrue _ = tskip
onFalse (tswitch _ b _ _) = b
onFalse _ = tskip
onPair (tswitch _ _ c _) = c
onPair _ = tskip
otherwise (tswitch _ _ _ d) = d
otherwise _ = tskip

private
  TShape : Type ℓ-zero
  TShape = ℕ ⊎ ℕ

  TPos : Unit → TShape → Type ℓ-zero
  TPos _ (Sum.inl (suc (suc zero))) = Fin 4
  TPos _ _ = ⊥

  TW : Unit → Type ℓ-zero
  TW = IW (λ _ → TShape) TPos (λ _ _ _ → tt)

  isSetTW : isSet (TW tt)
  isSetTW = isOfHLevelSuc-IW 1 (λ _ → isSet⊎ isSetℕ isSetℕ) tt

  toT : Tree → TW tt
  toT tfail = node (Sum.inl 0) λ ()
  toT tskip = node (Sum.inl 1) λ ()
  toT (tleaf k) = node (Sum.inr k) λ ()
  toT (tswitch a b c d) = node (Sum.inl 2) λ where
    zero → toT a
    (suc zero) → toT b
    (suc (suc zero)) → toT c
    (suc (suc (suc zero))) → toT d

  fromT : TW tt → Tree
  fromT (node (Sum.inl zero) _) = tfail
  fromT (node (Sum.inl (suc zero)) _) = tskip
  fromT (node (Sum.inl (suc (suc zero))) sub) =
    tswitch (fromT (sub zero)) (fromT (sub (suc zero)))
            (fromT (sub (suc (suc zero)))) (fromT (sub (suc (suc (suc zero)))))
  fromT (node (Sum.inl (suc (suc (suc k)))) _) = tfail
  fromT (node (Sum.inr k) _) = tleaf k

  treeRet : (t : Tree) → fromT (toT t) ≡ t
  treeRet tfail = refl
  treeRet tskip = refl
  treeRet (tleaf k) = refl
  treeRet (tswitch a b c d) i =
    tswitch (treeRet a i) (treeRet b i) (treeRet c i) (treeRet d i)

isSetTree : isSet Tree
isSetTree = isOfHLevelRetract 2 toT fromT treeRet isSetTW


-- `pick` non-recursive is what keeps `runTree` structural in the tree.
pick : Tree → Maybe ℕ → Maybe ℕ → Maybe ℕ
pick tfail x _ = x
pick tskip _ y = y
pick (tleaf _) x _ = x
pick (tswitch _ _ _ _) x _ = x

runTree : Tree → Vals n → Maybe ℕ
runTree tfail _ = nothing
runTree tskip _ = nothing
runTree (tleaf k) _ = just k
runTree (tswitch _ _ _ _) ⟨⟩ = nothing
runTree (tswitch a b c d) (vtrue ▸ vs) = pick a (runTree a vs) (runTree d vs)
runTree (tswitch a b c d) (vfalse ▸ vs) = pick b (runTree b vs) (runTree d vs)
runTree (tswitch a b c d) (vpair x y ▸ vs) =
  pick c (runTree c (x ▸ y ▸ vs)) (runTree d vs)


-- Recursion, so a wrong shape is `⊥` with no constructor equation to invert.
Skip NotSkip : Tree → Type ℓ-zero
Skip tfail = ⊥
Skip tskip = Unit
Skip (tleaf _) = ⊥
Skip (tswitch _ _ _ _) = ⊥
NotSkip tfail = Unit
NotSkip tskip = ⊥
NotSkip (tleaf _) = Unit
NotSkip (tswitch _ _ _ _) = Unit

IsNil IsCons : Mat n → Type ℓ-zero
IsNil [] = Unit
IsNil (_ ∷ _) = ⊥
IsCons [] = ⊥
IsCons (_ ∷ _) = Unit

HdRhs : Mat n → ℕ → Type ℓ-zero
HdRhs [] _ = ⊥
HdRhs (r ∷ _) k = rhsOf r ≡ k

-- Branch iff the head column mentions the constructor, default iff not a
-- complete signature: both `heads`-determined, so the judgment is a prop.
Br Df : Bool → Tree → Type ℓ-zero → Type ℓ-zero
Br true t X = NotSkip t × X
Br false t _ = Skip t
Df true d _ = Skip d
Df false d X = NotSkip d × X

Ok : (n : ℕ) → Tree → Mat n → Type ℓ-zero
Ok n tfail P = IsNil P
Ok n tskip P = ⊥
Ok zero (tleaf k) P = HdRhs P k
Ok (suc n) (tleaf k) P = ⊥
Ok zero (tswitch _ _ _ _) P = ⊥
Ok (suc n) (tswitch a b c d) P = IsCons P
  × Br (heads P vtrueOp) a (Ok n a (spec vtrueOp P))
  × Br (heads P vfalseOp) b (Ok n b (spec vfalseOp P))
  × Br (heads P vpairOp) c (Ok (suc (suc n)) c (spec vpairOp P))
  × Df (complete P) d (Ok n d (dflt P))

-- The only fact about `Ok` extracted rather than projected.
okNotSkip : (t : Tree) {P : Mat n} → Ok n t P → NotSkip t
okNotSkip tfail _ = tt
okNotSkip tskip ok = ok
okNotSkip (tleaf _) _ = tt
okNotSkip (tswitch _ _ _ _) _ = tt

private
  isPropSkip : (t : Tree) → isProp (Skip t)
  isPropSkip tfail = isProp⊥
  isPropSkip tskip = isPropUnit
  isPropSkip (tleaf _) = isProp⊥
  isPropSkip (tswitch _ _ _ _) = isProp⊥

  isPropNotSkip : (t : Tree) → isProp (NotSkip t)
  isPropNotSkip tfail = isPropUnit
  isPropNotSkip tskip = isProp⊥
  isPropNotSkip (tleaf _) = isPropUnit
  isPropNotSkip (tswitch _ _ _ _) = isPropUnit

  isPropIsNil : (P : Mat n) → isProp (IsNil P)
  isPropIsNil [] = isPropUnit
  isPropIsNil (_ ∷ _) = isProp⊥

  isPropIsCons : (P : Mat n) → isProp (IsCons P)
  isPropIsCons [] = isProp⊥
  isPropIsCons (_ ∷ _) = isPropUnit

  isPropHdRhs : (P : Mat n) (k : ℕ) → isProp (HdRhs P k)
  isPropHdRhs [] _ = isProp⊥
  isPropHdRhs (r ∷ _) k = isSetℕ (rhsOf r) k

isPropBr : (b : Bool) (t : Tree) (X : Type ℓ-zero) → isProp X → isProp (Br b t X)
isPropBr true t X pX = isProp× (isPropNotSkip t) pX
isPropBr false t X _ = isPropSkip t

isPropDf : (b : Bool) (t : Tree) (X : Type ℓ-zero) → isProp X → isProp (Df b t X)
isPropDf true t X _ = isPropSkip t
isPropDf false t X pX = isProp× (isPropNotSkip t) pX

isPropOk : (n : ℕ) (t : Tree) (P : Mat n) → isProp (Ok n t P)
isPropOk n tfail P = isPropIsNil P
isPropOk n tskip P = isProp⊥
isPropOk zero (tleaf k) P = isPropHdRhs P k
isPropOk (suc n) (tleaf k) P = isProp⊥
isPropOk zero (tswitch _ _ _ _) P = isProp⊥
isPropOk (suc n) (tswitch a b c d) P = isProp× (isPropIsCons P)
  (isProp× (isPropBr _ a _ (isPropOk n a (spec vtrueOp P)))
  (isProp× (isPropBr _ b _ (isPropOk n b (spec vfalseOp P)))
  (isProp× (isPropBr _ c _ (isPropOk (suc (suc n)) c (spec vpairOp P)))
           (isPropDf _ d _ (isPropOk n d (dflt P))))))


-- All constant in the model element: the matrix is fixed by the cover cell.
Comp : (n : ℕ) → TheoryTy ℓ-zero n
Comp n P = Σ[ t ∈ Tree ] Ok n t P

CompSet : (n : ℕ) → TheorySet ℓ-zero n
CompSet n = Comp n
  , λ P → isSetΣ isSetTree λ t → isProp→isSet (isPropOk n t P)

BrTy : (n : ℕ) (o : VOp) (b : Bool) (P : Mat (suc n)) → Type ℓ-zero
BrTy n o b P = Σ[ t ∈ Tree ] Br b t (Ok (VAr o + n) t (spec o P))

BrSet : (n : ℕ) (o : VOp) (b : Bool) (P : Mat (suc n))
      → TheorySet ℓ-zero (suc n)
BrSet n o b P = (λ _ → BrTy n o b P)
  , λ _ → isSetΣ isSetTree λ t → isProp→isSet
      (isPropBr b t _ (isPropOk (VAr o + n) t (spec o P)))

DfTy : (n : ℕ) (b : Bool) (P : Mat (suc n)) → Type ℓ-zero
DfTy n b P = Σ[ t ∈ Tree ] Df b t (Ok n t (dflt P))

DfSet : (n : ℕ) (b : Bool) (P : Mat (suc n)) → TheorySet ℓ-zero (suc n)
DfSet n b P = (λ _ → DfTy n b P)
  , λ _ → isSetΣ isSetTree λ t → isProp→isSet
      (isPropDf b t _ (isPropOk n t (dflt P)))

-- No side condition: every condition consulted is an index of the grammars.
SwSet : (n : ℕ) (P : Mat (suc n)) → TheorySet ℓ-zero (suc n)
SwSet n P = BrSet n vtrueOp (heads P vtrueOp) P
  &Set (BrSet n vfalseOp (heads P vfalseOp) P
  &Set (BrSet n vpairOp (heads P vpairOp) P
  &Set DfSet n (complete P) P))
