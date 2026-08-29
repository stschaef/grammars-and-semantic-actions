{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- What the combinators ask of the stack theory: precision of every
   operation, a cover of the model, and a well-founded order.

   The cover is the node cover, one cell per head equation plus a cell for
   the empty stack -- `UOp` is infinite, since `consOp n p` carries a
   problem, and a `Cover` does not care.  Note what the cover does *not*
   do: it does not look inside the head equation.  Reading `var`/`leaf`/
   `fork` is `flat1`'s job, and the checker branches on `flat1`'s answer,
   not on the term.  So the case analysis the framework sees has three
   cells -- clash, trivial, flexible -- which is what a machine has.

   The order is genuinely lexicographic, and this is the one place McBride's
   argument survives verbatim: the flexible rule solves an unknown, so its
   premise sits at a *smaller sort*, and every other rule leaves the sort
   alone and shortens the stack.  Because the scope is a sort rather than a
   number attached to a raw term, "the substitution eliminates a variable"
   needs no proof here at all.

   `Later/Indexed`'s `ilexOrder` is not the one to use: it measures
   `(size of the model, rank of the index)`, and the components here are
   the other way round -- the scope is an index and the stack is the model.
   `irankOrder` at `lexWFOrder ℕWF ℕWF` says so directly. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Type.Later.Indexed as LI
module Theory.Instances.Unify.Guard where

open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ)
open import Cubical.Data.Nat.WFOrder using (ℕWF)
open import Cubical.Data.Sigma using (ΣPathP ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Type.Later.Lex using (lexWFOrder)

open import Theory.Instances.Unify.Base public
open import Theory.Base UEqns ℕ (λ n → n) uPresentation public
open import Theory.Type.HLevels UEqns ℕ (λ n → n) uPresentation public
open import Theory.Type.Top.Base UEqns ℕ (λ n → n) uPresentation public
open import Theory.Type.Bottom.Base UEqns ℕ (λ n → n) uPresentation public
open import Theory.Type.Sum.Binary.Base UEqns ℕ (λ n → n) uPresentation public
open import Theory.Type.Product.Binary.Base UEqns ℕ (λ n → n) uPresentation
  public
open import Theory.Type.Cover.Base UEqns ℕ (λ n → n) uPresentation public
open import Theory.Type.Decidable.Base UEqns ℕ (λ n → n) uPresentation public
open import Theory.Combinator.Core UEqns ℕ (λ n → n) uPresentation public

-- the only argument position there is: what a `consOp` leaves behind
pattern theRest = zero

-- Total projections, so that cons injectivity is a `cong` rather than a
-- match on an equation between stacks.
tailOf : {n : ℕ} → Stack n → Stack n → Stack n
tailOf d [] = d
tailOf d (_ ∷ qs) = qs

private
  hd : {n : ℕ} → Prob n → Stack n → Prob n
  hd d [] = d
  hd d (q ∷ _) = q

  nilCode : {n : ℕ} → Stack n → Type ℓ-zero
  nilCode [] = Unit
  nilCode (_ ∷ _) = Empty.⊥

-- A cons is its head and its tail, so every operation is precise.
preciseU : (o : UOp) → Precise o
preciseU (n , p) m (ms , e) (ms' , e') =
  ΣPathP (funExt slot , isProp→PathP (λ _ → isPropModelEq) e e')
  where
  whole : p ∷ ms theRest ≡ p ∷ ms' theRest
  whole = Eq.eqToPath e ∙ sym (Eq.eqToPath e')

  slot : (a : Fin 1) → ms a ≡ ms' a
  slot theRest = cong (tailOf (ms theRest)) whole

-- The node cover: a stack is empty, or it is a cons at a named head.
Cell : (n : ℕ) → Maybe (Prob n) → TheoryTy ℓ-zero n
Cell n nothing ps = ps Eq.≡ []
Cell n (just p) = NodeAt (n , p)

stackCover : (n : ℕ) → Cover (Maybe (Prob n)) (Cell n)
stackCover n .total [] _ = nothing , Eq.refl
stackCover n .total (p ∷ ps) _ = just p , ((λ _ → ps) , Eq.refl)
stackCover n .disjoint nothing nothing ne = Empty.rec (ne Eq.refl)
stackCover n .disjoint nothing (just p) ne ps (e , (ms , e')) =
  Empty.rec (subst nilCode (sym cons≡nil) tt)
  where
  cons≡nil : p ∷ ms theRest ≡ []
  cons≡nil = Eq.eqToPath e' ∙ Eq.eqToPath e
stackCover n .disjoint (just p) nothing ne ps ((ms , e') , e) =
  Empty.rec (subst nilCode (sym cons≡nil) tt)
  where
  cons≡nil : p ∷ ms theRest ≡ []
  cons≡nil = Eq.eqToPath e' ∙ Eq.eqToPath e
stackCover n .disjoint (just p) (just p') ne ps ((ms , e) , (ms' , e')) =
  Empty.rec (ne (Eq.pathToEq (cong just same)))
  where
  same : p ≡ p'
  same = cong (hd p) (Eq.eqToPath e ∙ sym (Eq.eqToPath e'))

-- The guard.  The index is the scope, the model is the stack, and the
-- order is the lexicographic product in that order.
srt : ℕ → ℕ
srt n = n

order : LI.IPtOrder UEqns ℕ (λ n → n) uPresentation srt ℓ-zero
order = LI.irankOrder UEqns ℕ (λ n → n) uPresentation srt isSetℕ
  (lexWFOrder ℕWF ℕWF) (λ p → p .fst , stackSize (p .snd))

open LI.IPtOrder order using (_<_) public

-- the trivial-equation rule: same scope, one equation fewer
tailStep : {n : ℕ} {p : Prob n} {ps : Stack n} → (n , ps) < (n , p ∷ ps)
tailStep {p = p} {ps = ps} = lift (Sum.inr (refl , tail< p ps))

-- the flexible rule: an unknown is gone, and the stack may do what it likes
scopeStep : {n : ℕ} {ps' : Stack n} {ps : Stack (suc n)}
  → (n , ps') < (suc n , ps)
scopeStep = lift (Sum.inl (0 , refl))
