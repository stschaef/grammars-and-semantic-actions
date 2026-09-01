{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
-- Precision, cover, and order for the stack theory.  McBride's argument
-- survives verbatim: the flexible rule's premise sits at a SMALLER SORT, so
-- "the substitution eliminates a variable" needs no proof.  `ilexOrder`
-- measures the components the other way round, hence `irankOrder`.
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

-- total projections: cons injectivity is a `cong`, not an equation match
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

preciseU : (o : UOp) → Precise o
preciseU (n , p) m (ms , e) (ms' , e') =
  ΣPathP (funExt slot , isProp→PathP (λ _ → isPropModelEq) e e')
  where
  whole : p ∷ ms theRest ≡ p ∷ ms' theRest
  whole = Eq.eqToPath e ∙ sym (Eq.eqToPath e')

  slot : (a : Fin 1) → ms a ≡ ms' a
  slot theRest = cong (tailOf (ms theRest)) whole

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
