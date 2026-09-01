{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Decide the left-recursive `E → E + a | a` (which `Decidable/Productions` cannot take:
   `call` only answers at strict suffixes) by recognising `a (+ a)*` at `DecAnswer` and
   folding into `E` with the accumulator on the left. -}
open import Theory.Type.SemanticAction.Testing
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Examples.Theory.Combinator.LeftCornerLeftRec where

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)
import Cubical.Data.Maybe as MB

data Tok : Type where
  ‵a ‵+ : Tok

_≟T_ : (x y : Tok) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
‵a ≟T ‵a = Sum.inl Eq.refl
‵a ≟T ‵+ = Sum.inr λ ()
‵+ ≟T ‵a = Sum.inr λ ()
‵+ ≟T ‵+ = Sum.inl Eq.refl

open import Theory.Instances.Monoid.Combinator.Decidable.Base Tok _≟T_ ℓ-zero
open import Theory.Instances.Monoid.Combinator.Syntax Tok _≟T_ DecAnswer
open import Theory.Instances.Monoid.Residual Tok isSetAlphabet
  using (_⊸_ ; ⊸-lam ; ⊸-app ; ⊗ε-unit-r ; ⟦⊗e⟧ ; ⟦⊗e⟧⁻)

-- `Var tt` in the *leftmost* slot: the thing a predictive parser cannot call
private
  Ebr : Bool → Functor ℓM Unit (λ _ → tt) tt
  Ebr false = k (literal ‵a)
  Ebr true  = ⊗e _⊙_ (two (Var tt)
                          (⊗e _⊙_ (two (k (literal ‵+)) (k (literal ‵a)))))

  EC : Unit → Functor ℓM Unit (λ _ → tt) tt
  EC _ = ⊕e Bool Ebr

  isSetEbr : (b : Bool) → isSetValued (Ebr b)
  isSetEbr false = lift (isSetLiteral ‵a)
  isSetEbr true zero = lift tt*
  isSetEbr true (suc zero) zero = lift (isSetLiteral ‵+)
  isSetEbr true (suc zero) (suc zero) = lift (isSetLiteral ‵a)

  isSetEC : (u : Unit) → isSetValued (EC u)
  isSetEC u .fst = lift isSetBool
  isSetEC u .snd = isSetEbr

E : TheoryTy _ tt
E = μ EC tt

Eset : TheorySet _ tt
Eset = E , isSetμ EC isSetEC tt

atom : literal ‵a ⊢ E
atom = roll ∘⊢ σ⊕ false ∘⊢ liftTy

addA : E ⊗ (literal ‵+ ⊗ literal ‵a) ⊢ E
addA = roll ∘⊢ σ⊕ true
  ∘⊢ ⟦⊗e⟧⁻ (Var tt) (⊗e _⊙_ (two (k (literal ‵+)) (k (literal ‵a))))
  ∘⊢ (liftTy ,⊗ (⟦⊗e⟧⁻ (k (literal ‵+)) (k (literal ‵a))
                 ∘⊢ (liftTy ,⊗ liftTy)))

PA : TheorySet _ tt
PA = litSet ‵+ ⊗Set litSet ‵a

tails : ⊤Ty ⊢ Parser _ ⟨□⟩ ⟨□⟩ (StarSet PA)
tails = many ℓ-zero PA (seq (litSet ‵a) (pmore ∘⊢ tok ‵+) (tok ‵a))

flat : ⊤Ty ⊢ Parser _ ⟨□⟩ ⟨□⟩ (litSet ‵a ⊗Set StarSet PA)
flat = seq (StarSet PA) (pmore ∘⊢ tok ‵a) tails

decFlat : Decidable (literal ‵a ⊗ (ty PA *))
decFlat = runP _ flat

-- `E ⊸ E` is the stack of pending reductions; `⊸-app` is the reduction
foldTail : (ty PA *) ⊢ (E ⊸ E)
foldTail = fold*r nil' cons'
  where
  nil' : ⟦ starBranch (ty PA) false ⟧TheoryTy (λ _ → E ⊸ E) ⊢ (E ⊸ E)
  nil' = ⊸-lam {A = E} {B = εTy} {C = E} ⊗ε-unit-r ∘⊢ NIL-elim {A = ty PA}

  cons' : ⟦ starBranch (ty PA) true ⟧TheoryTy (λ _ → E ⊸ E) ⊢ (E ⊸ E)
  cons' =
    ⊸-lam {A = E} {B = ty PA ⊗ (E ⊸ E)} {C = E}
      (⊸-app {A = E} {C = E} ∘⊢ (addA ,⊗ id⊢) ∘⊢ ⊗-assoc⁻)
    ∘⊢ ((lowerTy ,⊗ lowerTy) ∘⊢ ⟦⊗e⟧ (k (ty PA)) (Var tt))

toE : literal ‵a ⊗ (ty PA *) ⊢ E
toE = ⊸-app {A = E} {C = E} ∘⊢ (atom ,⊗ foldTail)

-- the tree is read off `E` itself: `addL` is a genuine `E → E + a` node
data ETree : Type where
  lit  : ETree
  addL : ETree → ETree

private
  Ktree : Unit → TheoryTy ℓ-zero tt
  Ktree _ _ = ETree

  treeAlg : (u : Unit) → ⟦ EC u ⟧TheoryTy Ktree ⊢ Ktree u
  treeAlg _ = ⊕ᴰ-elim br
    where
    br : (b : Bool) → ⟦ Ebr b ⟧TheoryTy Ktree ⊢ Ktree tt
    br false m z = lit
    br true m (ms , e , h) = addL (h zero .lower)

readE : E ⊢ Ktree tt
readE = rec EC treeAlg tt

parseE : String → MB.Maybe ETree
parseE = observe decFlat (semact-dec (λ m z → readE m (toE m z) , tt))

left-recursive-trees : passes
  (parseE at
    ( (‵a ∷ [])                               ↦ MB.just lit
    ∷ (‵a ∷ ‵+ ∷ ‵a ∷ [])                     ↦ MB.just (addL lit)
    ∷ (‵a ∷ ‵+ ∷ ‵a ∷ ‵+ ∷ ‵a ∷ [])           ↦ MB.just (addL (addL lit))
    ∷ (‵a ∷ ‵a ∷ [])                          ↦ MB.nothing
    ∷ (‵+ ∷ ‵a ∷ [])                          ↦ MB.nothing
    ∷ (‵a ∷ ‵+ ∷ [])                          ↦ MB.nothing
    ∷ [] ))
left-recursive-trees = refl
