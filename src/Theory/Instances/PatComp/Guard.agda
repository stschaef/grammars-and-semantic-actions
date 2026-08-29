{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- What the combinators ask of the matrix theory: precision of every
   operation, a cover of the model, and a well-founded order.

   The cover is the node cover, one cell per head ROW plus a cell for the
   empty matrix.  Note what it does not do: it does not look at the head
   COLUMN.  Reading the column is `heads`' job, and the checker branches on
   `heads`' answer, not on a row -- so the case analysis the framework sees
   has two cells, empty and non-empty, and everything else is a decision
   about a boolean the client computed.  That is what a machine looks like
   from the framework's side, and it is why `Ans-node` never fires here:
   the one premise the cover could supply, at the tail of the matrix, is a
   premise of no rule of the algorithm.

   The order is `ilexOrder` and not `Unify`'s `irankOrder`, and the
   difference is exactly the one `Unify/Guard`'s header names.  There the
   components were (index, model) -- the scope drops and the stack does
   what it likes.  Here they are (model, index): the constructor count of
   the matrix drops at every specialisation, and the WIDTH is the tiebreak
   for the one step that leaves the count alone, the default taken at a
   head column of nothing but wildcards.  `ilexOrder` measures precisely
   (size of the model, rank of the index), so it is the order to use
   without any repackaging.

   The width is only a tiebreak and could not be a measure: specialising on
   a pair takes `suc n` columns to `2 + n`, so the width GROWS in the case
   that matters most. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Type.Later.Indexed as LI
module Theory.Instances.PatComp.Guard where

open import Cubical.Data.Bool using (Bool ; true ; false ; Bool→Type)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; isSetℕ ; +-suc)
import Cubical.Data.Nat.Order as NO
open import Cubical.Data.Sigma using (ΣPathP ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.PatComp.Base public
open import Theory.Base MEqns ℕ (λ n → n) mPresentation public
  hiding (Val)
open import Theory.Type.HLevels MEqns ℕ (λ n → n) mPresentation public
open import Theory.Type.Top.Base MEqns ℕ (λ n → n) mPresentation public
open import Theory.Type.Bottom.Base MEqns ℕ (λ n → n) mPresentation public
open import Theory.Type.Sum.Binary.Base MEqns ℕ (λ n → n) mPresentation public
open import Theory.Type.Product.Binary.Base MEqns ℕ (λ n → n) mPresentation
  public
open import Theory.Type.Cover.Base MEqns ℕ (λ n → n) mPresentation public
open import Theory.Type.Decidable.Base MEqns ℕ (λ n → n) mPresentation public
open import Theory.Combinator.Core MEqns ℕ (λ n → n) mPresentation public

-- the only argument position there is: what a row leaves behind
pattern theRest = zero

-- Total projections, so that cons injectivity is a `cong` rather than a
-- match on an equation between matrices.
tailOf : {n : ℕ} → Mat n → Mat n → Mat n
tailOf d [] = d
tailOf d (_ ∷ Q) = Q

private
  hd : {n : ℕ} → Row n → Mat n → Row n
  hd d [] = d
  hd d (r ∷ _) = r

  nilCode : {n : ℕ} → Mat n → Type ℓ-zero
  nilCode [] = Unit
  nilCode (_ ∷ _) = Empty.⊥

-- A matrix is its head row and the rest, so every operation is precise.
-- Unused, as it happens: `Ans-node` is the one combinator this client has
-- no rule for.
preciseM : (o : MOp) → Precise o
preciseM (n , r) m (ms , e) (ms' , e') =
  ΣPathP (funExt slot , isProp→PathP (λ _ → isPropModelEq) e e')
  where
  whole : r ∷ ms theRest ≡ r ∷ ms' theRest
  whole = Eq.eqToPath e ∙ sym (Eq.eqToPath e')

  slot : (a : Fin 1) → ms a ≡ ms' a
  slot theRest = cong (tailOf (ms theRest)) whole

-- The node cover: a matrix is empty, or it is a cons at a named row.
Cell : (n : ℕ) → Maybe (Row n) → TheoryTy ℓ-zero n
Cell n nothing P = P Eq.≡ []
Cell n (just r) = NodeAt (n , r)

matCover : (n : ℕ) → Cover (Maybe (Row n)) (Cell n)
matCover n .total [] _ = nothing , Eq.refl
matCover n .total (r ∷ P) _ = just r , ((λ _ → P) , Eq.refl)
matCover n .disjoint nothing nothing ne = Empty.rec (ne Eq.refl)
matCover n .disjoint nothing (just r) ne P (e , (ms , e')) =
  Empty.rec (subst nilCode (sym cons≡nil) tt)
  where
  cons≡nil : r ∷ ms theRest ≡ []
  cons≡nil = Eq.eqToPath e' ∙ Eq.eqToPath e
matCover n .disjoint (just r) nothing ne P ((ms , e') , e) =
  Empty.rec (subst nilCode (sym cons≡nil) tt)
  where
  cons≡nil : r ∷ ms theRest ≡ []
  cons≡nil = Eq.eqToPath e' ∙ Eq.eqToPath e
matCover n .disjoint (just r) (just r') ne P ((ms , e) , (ms' , e')) =
  Empty.rec (ne (Eq.pathToEq (cong just same)))
  where
  same : r ≡ r'
  same = cong (hd r) (Eq.eqToPath e ∙ sym (Eq.eqToPath e'))

-- The guard.  The index is the width, the model is the matrix, and the
-- order is the lexicographic product in that order.
srt : ℕ → ℕ
srt n = n

order : LI.IPtOrder MEqns ℕ (λ n → n) mPresentation srt ℓ-zero
order = LI.ilexOrder MEqns ℕ (λ n → n) mPresentation srt isSetℕ
  (λ _ → msize) (λ n → n)

open LI.IPtOrder order using (_<_) public

private
  leCase : {a b : ℕ} → a NO.≤ b → (a ≡ b) Sum.⊎ (a NO.< b)
  leCase (zero , p) = Sum.inl p
  leCase {a} (suc k , p) = Sum.inr (k , +-suc k a ∙ p)

-- Named, because a position of the order is a `Σ` behind two module
-- applications and does not elaborate from a pair literal at the call
-- sites; only the two descents below ever need to name one.
SpecDesc : {n : ℕ} (o : VOp) (P : Mat (suc n)) → Type _
SpecDesc {n} o P = (VAr o + n , spec o P) < (suc n , P)

DfltDesc : {n : ℕ} (P : Mat (suc n)) → Type _
DfltDesc {n} P = (n , dflt P) < (suc n , P)

-- Specialisation: the constructor count drops, so the width may do what it
-- likes -- and at a pair it grows.
specDesc : {n : ℕ} (o : VOp) (P : Mat (suc n)) → Bool→Type (heads P o)
  → SpecDesc o P
specDesc o P h = lift (Sum.inl (spec< o P h))

-- The default: the count never grows, and the width always drops.  The two
-- disjuncts of the lexicographic order are the two cases of `leCase`, and
-- the second one -- count unchanged -- is the head column of nothing but
-- wildcards that the width is in the order to rule out.
dfltDesc : {n : ℕ} (P : Mat (suc n)) → DfltDesc P
dfltDesc P = lift
  (Sum.rec (λ e → Sum.inr (e , NO.≤-refl)) Sum.inl (leCase (dflt≤ P)))
