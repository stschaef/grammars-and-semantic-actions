{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The experiment: can a *left-recursive* grammar be decided, with its own
   trees, by deciding a left-factored state grammar and letting the residual
   build the value?

     E → E + a | a

   `Decidable/Productions` cannot take this: `call y` may only be consulted at
   a strict suffix, and the leading item of `E → E + a` is `E` itself at the
   same suffix.  The claim under test is that the fix is *not* a new parser
   type but a change of what the fixpoint is indexed by -- states rather than
   nonterminals -- with the states left-factored so that each one consumes a
   terminal before recursing, and the left-recursive value rebuilt by
   accumulating on the left, which is what `⊸` is for.

   So: recognise `a (+ a)*` with `Core`'s combinators at `DecAnswer`, and
   fold it into `E` with the accumulator on the left.  Nothing here decides
   anything about a stack, which is what made the residual formulation
   undecidable. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.LeftCorner.LeftRec where

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

-- THE LEFT-RECURSIVE GRAMMAR.  `Var tt` sits in the *leftmost* slot of the
-- second production: this is the thing a predictive parser cannot call.
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

-- its two productions, as terms
atom : literal ‵a ⊢ E
atom = roll ∘⊢ σ⊕ false ∘⊢ liftTy

addA : E ⊗ (literal ‵+ ⊗ literal ‵a) ⊢ E
addA = roll ∘⊢ σ⊕ true
  ∘⊢ ⟦⊗e⟧⁻ (Var tt) (⊗e _⊙_ (two (k (literal ‵+)) (k (literal ‵a))))
  ∘⊢ (liftTy ,⊗ (⟦⊗e⟧⁻ (k (literal ‵+)) (k (literal ‵a))
                 ∘⊢ (liftTy ,⊗ liftTy)))

-- THE STATE GRAMMAR, left-factored: `+ a`, and the state loops on it.
PA : TheorySet _ tt
PA = litSet ‵+ ⊗Set litSet ‵a

tails : ⊤Ty ⊢ Parser _ ⟨□⟩ ⟨□⟩ (StarSet PA)
tails = many ℓ-zero PA (seq (litSet ‵a) (pmore ∘⊢ tok ‵+) (tok ‵a))

flat : ⊤Ty ⊢ Parser _ ⟨□⟩ ⟨□⟩ (litSet ‵a ⊗Set StarSet PA)
flat = seq (StarSet PA) (pmore ∘⊢ tok ‵a) tails

-- ...and it is decidable, because nothing negative was ever decided.
decFlat : Decidable (literal ‵a ⊗ (ty PA *))
decFlat = runP _ flat

-- THE ASCENT: rebuild the left-recursive value, accumulating on the left.
-- `E ⊸ E` is "an `E` is owed on my left, and I will return an `E`" -- which
-- is exactly a stack of pending reductions, and `⊸-app` is the reduction.
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

-- ...and it runs.  The tree is read off `E` itself, so a `left` in the output
-- is a genuine `E → E + a` node: the left-recursive grammar's own parse.
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
