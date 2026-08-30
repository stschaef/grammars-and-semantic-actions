{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The scaling test: the arithmetic expression grammar.

     E → E + T | T          T → ( E ) | x

   Non-regular (the parens need a stack), left-recursive (not LL as given),
   and mutually recursive (so the fixpoint has more than one index -- nothing
   so far has).  `LeftCorner/LeftRec` and `LeftCorner/Defer` both turned out to be regular, so
   this is the first example where the recipe has to survive a real pushdown.

   The skeleton is the left-corner transform, in the form `Decidable/Productions`
   demands: every production begins with a terminal.

     E' → ( E' ) R | x R    R → + T' R | ε    T' → ( E' ) | x

   That is classical left-recursion elimination, so the interest is not that
   it exists but that the value recovered from it is a parse of the *original*
   `E`, built by accumulating on the left with `⊸`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.LeftCorner.Expr where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)
import Cubical.Data.Maybe as MB

open import Theory.Instances.Monoid.Combinator.ExprGrammar
open import Theory.Instances.Monoid.Combinator.Decidable.Synthesis Tk _≟K_
open import Theory.Instances.Monoid.Residual Tk isSetAlphabet
  using (_⊸_ ; ⊸-lam ; ⊸-app ; ⊗ε-unit-r ; ⟦⊗e⟧)

-- THE SKELETON.  Every production is led by a terminal, which is exactly the
-- form `Decidable/Productions` demands -- so the recogniser is not hand-rolled
-- here, it is the repo's own LL(1) generator applied to the left-corner
-- transform, with the table itself synthesised from the rules below.
data SK : Type where
  sE sR sT : SK

decSK : DiscreteEq SK
decSK sE sE = Sum.inl Eq.refl
decSK sR sR = Sum.inl Eq.refl
decSK sT sT = Sum.inl Eq.refl
decSK sE sR = Sum.inr λ ()
decSK sE sT = Sum.inr λ ()
decSK sR sE = Sum.inr λ ()
decSK sR sT = Sum.inr λ ()
decSK sT sE = Sum.inr λ ()
decSK sT sR = Sum.inr λ ()

-- The grammar, as rules rather than as a table.  `Synthesis` turns this into
-- the `Table` that `Gen` wants and, more to the point, *computes* whether it
-- is LL(1); before, conflict-freedom was implicit in being able to write the
-- table out, which is a property of the author rather than of the grammar.
exprRules : Rules SK
exprRules .Rules.nullable sE = false
exprRules .Rules.nullable sR = true
exprRules .Rules.nullable sT = false
exprRules .Rules.of sE =
    (‵lp , nt sE ∷ tm ‵rp ∷ nt sR ∷ [])
  ∷ (‵x  , nt sR ∷ [])
  ∷ []
exprRules .Rules.of sR = (‵+ , nt sT ∷ nt sR ∷ []) ∷ []
exprRules .Rules.of sT =
    (‵lp , nt sE ∷ tm ‵rp ∷ [])
  ∷ (‵x  , [])
  ∷ []

module ES = Synth (sE ∷ sR ∷ sT ∷ []) exprRules

-- ...and the LL(1) certificate, by computation.  `Eq.refl` here is the whole
-- check: no nonterminal has two rules led by the same terminal.
exprLL1 : ES.clashes Eq.≡ []
exprLL1 = Eq.refl

exprTable : Table SK
exprTable = ES.table

-- ...and the check has teeth.  Give `sT` a second rule led by `‵x` and the
-- clash is reported, rather than the first rule silently winning.
private
  badRules : Rules SK
  badRules .Rules.nullable = exprRules .Rules.nullable
  badRules .Rules.of sE = exprRules .Rules.of sE
  badRules .Rules.of sR = exprRules .Rules.of sR
  badRules .Rules.of sT = (‵x , []) ∷ exprRules .Rules.of sT

  module BS = Synth (sE ∷ sR ∷ sT ∷ []) badRules

  badClash : BS.clashes Eq.≡ ((sT , ‵x) ∷ [])
  badClash = Eq.refl

  badRejected : BS.synth Eq.≡ MB.nothing
  badRejected = Eq.refl

open Gen exprTable

-- the recogniser, straight out of `Decidable/Productions`
decExpr : Decidable (S sE)
decExpr = decide sE

accepts : String → Bool
accepts w = isYes (decExpr w tt)

skeleton-yes : passes
  (accepts at
    ( (‵x ∷ [])                                     ↦ true
    ∷ (‵x ∷ ‵+ ∷ ‵x ∷ [])                           ↦ true
    ∷ (‵x ∷ ‵+ ∷ ‵x ∷ ‵+ ∷ ‵x ∷ [])                 ↦ true
    ∷ (‵lp ∷ ‵x ∷ ‵rp ∷ [])                         ↦ true
    ∷ (‵lp ∷ ‵x ∷ ‵+ ∷ ‵x ∷ ‵rp ∷ ‵+ ∷ ‵x ∷ [])     ↦ true
    ∷ [] ))
skeleton-yes = refl

skeleton-no : passes
  (accepts at
    ( []                              ↦ false
    ∷ (‵+ ∷ [])                       ↦ false
    ∷ (‵x ∷ ‵+ ∷ [])                  ↦ false
    ∷ (‵lp ∷ ‵x ∷ [])                 ↦ false
    ∷ (‵x ∷ ‵x ∷ [])                  ↦ false
    ∷ (‵lp ∷ ‵rp ∷ [])                ↦ false
    ∷ [] ))
skeleton-no = refl

-- THE ASCENT.  The motive: `sE` and `sT` give the original grammar's trees,
-- and `sR` -- the `(+ T)*` tail -- gives `E ⊸ E`, an `E` owed on the left.
-- That is the stack of pending reductions, and `⊸-app` is the reduction.
Mot : SK → TheoryTy _ tt
Mot sE = E
Mot sR = E ⊸ E
Mot sT = Trm

private
  -- a body ends in `bodyCode [] = k εTy`; drop it
  dropε : {ℓ‵ : Level} {A : TheoryTy ℓ‵ tt}
    → A ⊗ ⟦ bodyCode [] ⟧TheoryTy Mot ⊢ A
  dropε = ⊗ε-unit-r ∘⊢ (id⊢ ,⊗ lowerTy)

  dead : {ℓ‵ : Level} {A : TheoryTy ℓ‵ tt}
    → ⟦ k (⊥Ty↑ ℓM) ⟧TheoryTy Mot ⊢ A
  dead = ⊥Ty↑-elim ∘⊢ lowerTy

  -- `( E ) R` and `x R`, the two ways to be an `E`
  parenE : ⟦ bodyCode (tm ‵lp ∷ nt sE ∷ tm ‵rp ∷ nt sR ∷ []) ⟧TheoryTy Mot ⊢ E
  parenE =
    ⊸-app {A = E} {C = E}
    ∘⊢ ((embE ∘⊢ parT) ,⊗ id⊢)
    ∘⊢ ⊗-assoc⁻ ∘⊢ (id⊢ ,⊗ ⊗-assoc⁻)
    ∘⊢ (lowerTy ,⊗ (lowerTy ,⊗ (lowerTy ,⊗ (dropε ∘⊢ (lowerTy ,⊗ id⊢)))))
    ∘⊢ (id⊢ ,⊗ (id⊢ ,⊗ (id⊢ ,⊗ ⟦⊗e⟧ {A = Mot} (itemCode (nt sR)) (bodyCode []))))
    ∘⊢ (id⊢ ,⊗ (id⊢ ,⊗ ⟦⊗e⟧ {A = Mot} (itemCode (tm ‵rp)) (bodyCode (nt sR ∷ []))))
    ∘⊢ (id⊢ ,⊗ ⟦⊗e⟧ {A = Mot} (itemCode (nt sE)) (bodyCode (tm ‵rp ∷ nt sR ∷ [])))
    ∘⊢ ⟦⊗e⟧ {A = Mot} (itemCode (tm ‵lp)) (bodyCode (nt sE ∷ tm ‵rp ∷ nt sR ∷ []))

  varE : ⟦ bodyCode (tm ‵x ∷ nt sR ∷ []) ⟧TheoryTy Mot ⊢ E
  varE =
    ⊸-app {A = E} {C = E}
    ∘⊢ ((embE ∘⊢ varT) ,⊗ id⊢)
    ∘⊢ (lowerTy ,⊗ (dropε ∘⊢ (lowerTy ,⊗ id⊢)))
    ∘⊢ (id⊢ ,⊗ ⟦⊗e⟧ {A = Mot} (itemCode (nt sR)) (bodyCode []))
    ∘⊢ ⟦⊗e⟧ {A = Mot} (itemCode (tm ‵x)) (bodyCode (nt sR ∷ []))

  -- `+ T R`: the reduction `E → E + T`, with the accumulated `E` on the left
  addR : ⟦ bodyCode (tm ‵+ ∷ nt sT ∷ nt sR ∷ []) ⟧TheoryTy Mot ⊢ (E ⊸ E)
  addR =
    ⊸-lam {A = E} {B = literal ‵+ ⊗ (Trm ⊗ (E ⊸ E))} {C = E}
      (⊸-app {A = E} {C = E} ∘⊢ (addE ,⊗ id⊢) ∘⊢ ⊗-assoc⁻ ∘⊢ (id⊢ ,⊗ ⊗-assoc⁻))
    ∘⊢ (lowerTy ,⊗ (lowerTy ,⊗ (dropε ∘⊢ (lowerTy ,⊗ id⊢))))
    ∘⊢ (id⊢ ,⊗ (id⊢ ,⊗ ⟦⊗e⟧ {A = Mot} (itemCode (nt sR)) (bodyCode [])))
    ∘⊢ (id⊢ ,⊗ ⟦⊗e⟧ {A = Mot} (itemCode (nt sT)) (bodyCode (nt sR ∷ [])))
    ∘⊢ ⟦⊗e⟧ {A = Mot} (itemCode (tm ‵+)) (bodyCode (nt sT ∷ nt sR ∷ []))

  nilR : ⟦ nulCode true ⟧TheoryTy Mot ⊢ (E ⊸ E)
  nilR = ⊸-lam {A = E} {B = εTy} {C = E} ⊗ε-unit-r ∘⊢ lowerTy

  parenT : ⟦ bodyCode (tm ‵lp ∷ nt sE ∷ tm ‵rp ∷ []) ⟧TheoryTy Mot ⊢ Trm
  parenT =
    parT
    ∘⊢ (lowerTy ,⊗ (lowerTy ,⊗ (dropε ∘⊢ (lowerTy ,⊗ id⊢))))
    ∘⊢ (id⊢ ,⊗ (id⊢ ,⊗ ⟦⊗e⟧ {A = Mot} (itemCode (tm ‵rp)) (bodyCode [])))
    ∘⊢ (id⊢ ,⊗ ⟦⊗e⟧ {A = Mot} (itemCode (nt sE)) (bodyCode (tm ‵rp ∷ [])))
    ∘⊢ ⟦⊗e⟧ {A = Mot} (itemCode (tm ‵lp)) (bodyCode (nt sE ∷ tm ‵rp ∷ []))

  varT' : ⟦ bodyCode (tm ‵x ∷ []) ⟧TheoryTy Mot ⊢ Trm
  varT' = varT ∘⊢ lowerTy ∘⊢ dropε ∘⊢ ⟦⊗e⟧ {A = Mot} (itemCode (tm ‵x)) (bodyCode [])

  alg : (x : SK) → ⟦ F x ⟧TheoryTy Mot ⊢ Mot x
  alg sE = ⊕ᴰ-elim λ where
    MB.nothing        → dead
    (MB.just (tk ‵lp)) → parenE
    (MB.just (tk ‵x))  → varE
    (MB.just (tk ‵+))  → dead
    (MB.just (tk ‵rp)) → dead
    (MB.just ε₁)       → dead
  alg sR = ⊕ᴰ-elim λ where
    MB.nothing        → nilR
    (MB.just (tk ‵+))  → addR
    (MB.just (tk ‵x))  → dead
    (MB.just (tk ‵lp)) → dead
    (MB.just (tk ‵rp)) → dead
    (MB.just ε₁)       → dead
  alg sT = ⊕ᴰ-elim λ where
    MB.nothing        → dead
    (MB.just (tk ‵lp)) → parenT
    (MB.just (tk ‵x))  → varT'
    (MB.just (tk ‵+))  → dead
    (MB.just (tk ‵rp)) → dead
    (MB.just ε₁)       → dead

toOriginal : (x : SK) → S x ⊢ Mot x
toOriginal = rec F alg

-- ...and read the original grammar's trees off.  `add` is a genuine
-- `E → E + T` node, so a left-leaning `add (add _ _) _` is the left-recursive
-- parse -- the thing the skeleton no longer has.
parseExpr : String → MB.Maybe Ex
parseExpr = observe decExpr
  (semact-dec (λ m z → readG nE m (toOriginal sE m z) , tt))

-- LEFT-associated: `x + x + x` is `add (add _ _) _`, not `add _ (add _ _)`.
expr-trees : passes
  (parseExpr at
    ( (‵x ∷ [])                             ↦ MB.just (emb var)
    ∷ (‵x ∷ ‵+ ∷ ‵x ∷ [])                   ↦ MB.just (add (emb var) var)
    ∷ (‵x ∷ ‵+ ∷ ‵x ∷ ‵+ ∷ ‵x ∷ [])         ↦ MB.just (add (add (emb var) var) var)
    ∷ (‵lp ∷ ‵x ∷ ‵rp ∷ [])                 ↦ MB.just (emb (par (emb var)))
    ∷ (‵lp ∷ ‵x ∷ ‵+ ∷ ‵x ∷ ‵rp ∷ ‵+ ∷ ‵x ∷ [])
        ↦ MB.just (add (emb (par (add (emb var) var))) var)
    ∷ [] ))
expr-trees = refl

expr-rejects : passes
  (parseExpr at
    ( []                              ↦ MB.nothing
    ∷ (‵+ ∷ [])                       ↦ MB.nothing
    ∷ (‵x ∷ ‵+ ∷ [])                  ↦ MB.nothing
    ∷ (‵lp ∷ ‵x ∷ [])                 ↦ MB.nothing
    ∷ (‵x ∷ ‵x ∷ [])                  ↦ MB.nothing
    ∷ [] ))
expr-rejects = refl
