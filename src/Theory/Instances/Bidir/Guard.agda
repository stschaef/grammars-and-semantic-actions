{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The two modes call each other at the SAME term, so `ilexOrder` orders
   (index, model) by (size model, rank index); `modeStep` drops the rank
   while the term stands still.  `Chk` must rank below `Syn`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Type.Later.Indexed as LI
module Theory.Instances.Bidir.Guard where

open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-comm ; +-suc)
import Cubical.Data.Nat.Order as NO
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Sigma using (ΣPathP ; _,_ ; fst ; snd)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Bidir.Base public
open import Theory.Base BEqns ℕ (λ _ → nm) bPresentation public
open import Theory.Type.HLevels BEqns ℕ (λ _ → nm) bPresentation public
open import Theory.Type.Top.Base BEqns ℕ (λ _ → nm) bPresentation public
open import Theory.Type.Bottom.Base BEqns ℕ (λ _ → nm) bPresentation public
open import Theory.Type.Sum.Base BEqns ℕ (λ _ → nm) bPresentation public
open import Theory.Type.Sum.Binary.Base BEqns ℕ (λ _ → nm) bPresentation public
open import Theory.Type.Product.Base BEqns ℕ (λ _ → nm) bPresentation public
open import Theory.Type.Product.Binary.Base BEqns ℕ (λ _ → nm) bPresentation public
open import Theory.Type.Cover.Base BEqns ℕ (λ _ → nm) bPresentation public
open import Theory.Type.Decidable.Base BEqns ℕ (λ _ → nm) bPresentation public
open import Theory.Type.Decidable.Route BEqns ℕ (λ _ → nm) bPresentation public
open import Theory.Combinator.Core BEqns ℕ (λ _ → nm) bPresentation public

private variable ℓX : Level

-- argument positions, as pattern synonyms
pattern theVar    = zero        -- varOp:   the name
pattern theFun    = zero        -- appOp:   the function
pattern theArg    = suc zero    -- appOp:   the argument
pattern theBinder = zero        -- lamOp B: the bound name
pattern theBody   = suc zero    -- lamOp B: the body under it

-- Injectivity by projection: matching `Eq.refl` here is stuck without K.
varN : ℕ → BTm → ℕ
varN d (bvar x) = x
varN d (bapp _ _) = d
varN d (blam _ _ _) = d

appFun appArgOf : BTm → BTm
appFun (bvar x) = bvar x
appFun (bapp f _) = f
appFun (blam x B t) = blam x B t
appArgOf (bvar x) = bvar x
appArgOf (bapp _ a) = a
appArgOf (blam x B t) = blam x B t

lamN : ℕ → BTm → ℕ
lamN d (bvar _) = d
lamN d (bapp _ _) = d
lamN d (blam x _ _) = x

lamBd : BTm → BTm
lamBd (bvar x) = bvar x
lamBd (bapp f a) = bapp f a
lamBd (blam _ _ t) = t

preciseB : (o : BOp) → Precise o
preciseB varOp m (ms , e) (ms' , e') =
  ΣPathP (funExt slot , isProp→PathP (λ _ → isPropModelEq) e e')
  where
  whole : bvar (ms zero) ≡ bvar (ms' zero)
  whole = Eq.eqToPath e ∙ sym (Eq.eqToPath e')

  slot : (a : Fin 1) → ms a ≡ ms' a
  slot zero = cong (varN (ms zero)) whole
preciseB appOp m (ms , e) (ms' , e') =
  ΣPathP (funExt slot , isProp→PathP (λ _ → isPropModelEq) e e')
  where
  whole : bapp (ms zero) (ms (suc zero)) ≡ bapp (ms' zero) (ms' (suc zero))
  whole = Eq.eqToPath e ∙ sym (Eq.eqToPath e')

  slot : (a : Fin 2) → ms a ≡ ms' a
  slot zero = cong appFun whole
  slot (suc zero) = cong appArgOf whole
preciseB (lamOp B) m (ms , e) (ms' , e') =
  ΣPathP (funExt slot , isProp→PathP (λ _ → isPropModelEq) e e')
  where
  whole : blam (ms zero) B (ms (suc zero)) ≡ blam (ms' zero) B (ms' (suc zero))
  whole = Eq.eqToPath e ∙ sym (Eq.eqToPath e')

  slot : (a : Fin 2) → ms a ≡ ms' a
  slot zero = cong (lamN (ms zero)) whole
  slot (suc zero) = cong lamBd whole

bSize : BTm → ℕ
bSize (bvar _) = 1
bSize (bapp f a) = suc (bSize f + bSize a)
bSize (blam _ _ t) = suc (bSize t)

private
  fun< : (f a : BTm) → bSize f NO.< bSize (bapp f a)
  fun< f a = bSize a , (+-suc (bSize a) (bSize f)
    ∙ cong suc (+-comm (bSize a) (bSize f)))

  arg< : (f a : BTm) → bSize a NO.< bSize (bapp f a)
  arg< f a = bSize f , +-suc (bSize f) (bSize a)

  body< : (x : ℕ) (B : Ty) (t : BTm) → bSize t NO.< bSize (blam x B t)
  body< x B t = 0 , refl

module Subterm {X : Type ℓX} (isSetX : isSet X) (rank : X → ℕ) where

  srt : X → BSort
  srt _ = tm

  order : LI.IPtOrder BEqns ℕ (λ _ → nm) bPresentation srt ℓ-zero
  order = LI.ilexOrder BEqns ℕ (λ _ → nm) bPresentation srt
    isSetX (λ _ → bSize) rank

  open LI.IPtOrder order using (_<_) public

  smaller : {x x' : X} {t t' : BTm}
    → bSize t' NO.< bSize t → (x' , t') < (x , t)
  smaller lt = lift (Sum.inl lt)

  -- the mode change: same term, smaller rank
  modeStep : {x x' : X} {t : BTm} → rank x' NO.< rank x → (x' , t) < (x , t)
  modeStep lt = lift (Sum.inr (refl , lt))

  callFun : {x x' : X} (f a : BTm) → (x' , f) < (x , bapp f a)
  callFun f a = smaller (fun< f a)

  callArg : {x x' : X} (f a : BTm) → (x' , a) < (x , bapp f a)
  callArg f a = smaller (arg< f a)

  callBody : {x x' : X} (n : ℕ) (B : Ty) (t : BTm)
    → (x' , t) < (x , blam n B t)
  callBody n B t = smaller (body< n B t)

appArgs : BTm → BTm → (b : Fin 2) → ↓M (SortOf appOp b)
appArgs u v theFun = u
appArgs u v theArg = v

lamArgs : (B : Ty) → ℕ → BTm → (b : Fin 2) → ↓M (SortOf (lamOp B) b)
lamArgs B y u theBinder = y
lamArgs B y u theBody = u

clsB : BTm → BOp
clsB (bvar _) = varOp
clsB (bapp _ _) = appOp
clsB (blam _ B _) = lamOp B

clsB-node : (o : BOp) (ms : interpIn o ↓M) → clsB (op o ms) ≡ o
clsB-node varOp ms = refl
clsB-node appOp ms = refl
clsB-node (lamOp B) ms = refl

nodeCover : Cover BOp NodeAt
nodeCover .total (bvar x) _ = varOp , ((λ _ → x) , Eq.refl)
nodeCover .total (bapp f a) _ = appOp , (appArgs f a , Eq.refl)
nodeCover .total (blam x B t) _ = lamOp B , (lamArgs B x t , Eq.refl)
nodeCover .disjoint o o' ne m ((ms , e) , (ms' , e')) =
  Empty.rec (ne (Eq.pathToEq same))
  where
  same : o ≡ o'
  same = sym (clsB-node o ms)
       ∙ cong clsB (Eq.eqToPath e ∙ sym (Eq.eqToPath e'))
       ∙ clsB-node o' ms'
