{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- Types as a theory: the model is the type language, so `Resolve` is
-- syntax-directed on a TYPE.  `V` is `⊥`: open types would make instance
-- resolution undecidable.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns
import Theory.Type.Later.Indexed as LI
module Theory.Instances.Class.Base where

open import Cubical.Data.Empty using (⊥)
import Cubical.Data.Empty as Empty
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-comm ; +-suc)
import Cubical.Data.Nat.Order as NO
open import Cubical.Data.Sigma using (ΣPathP ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Sum as Sum
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no ; Discrete)
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)

private variable ℓX : Level

-- `lst`: `Eq a => Eq (List a)` is the one rule with a smaller-type premise.
infixr 25 _⇒_
data Typ : Type ℓ-zero where
  ι : Typ
  lst : Typ → Typ
  _⇒_ : Typ → Typ → Typ

-- no-confusion via total projections, as in `Annotated/Base`
IsI IsL IsA : Typ → Type ℓ-zero
IsI ι = Unit
IsI (lst _) = ⊥
IsI (_ ⇒ _) = ⊥
IsL ι = ⊥
IsL (lst _) = Unit
IsL (_ ⇒ _) = ⊥
IsA ι = ⊥
IsA (lst _) = ⊥
IsA (_ ⇒ _) = Unit

elemOf domOf codOf : Typ → Typ
elemOf ι = ι
elemOf (lst a) = a
elemOf (a ⇒ _) = a
domOf ι = ι
domOf (lst a) = a
domOf (a ⇒ _) = a
codOf ι = ι
codOf (lst a) = a
codOf (_ ⇒ b) = b

discreteTyp : Discrete Typ
discreteTyp ι ι = yes refl
discreteTyp ι (lst _) = no λ p → subst IsI p tt
discreteTyp ι (_ ⇒ _) = no λ p → subst IsI p tt
discreteTyp (lst _) ι = no λ p → subst IsL p tt
discreteTyp (lst a) (lst a') = onElem (discreteTyp a a')
  where
  onElem : Dec (a ≡ a') → Dec (lst a ≡ lst a')
  onElem (yes p) = yes (cong lst p)
  onElem (no ¬p) = no λ e → ¬p (cong elemOf e)
discreteTyp (lst _) (_ ⇒ _) = no λ p → subst IsL p tt
discreteTyp (_ ⇒ _) ι = no λ p → subst IsA p tt
discreteTyp (_ ⇒ _) (lst _) = no λ p → subst IsA p tt
discreteTyp (a ⇒ b) (a' ⇒ b') = onParts (discreteTyp a a') (discreteTyp b b')
  where
  onParts : Dec (a ≡ a') → Dec (b ≡ b') → Dec ((a ⇒ b) ≡ (a' ⇒ b'))
  onParts (yes p) (yes q) = yes (cong₂ _⇒_ p q)
  onParts (no ¬p) _ = no λ e → ¬p (cong domOf e)
  onParts _ (no ¬q) = no λ e → ¬q (cong codOf e)

isSetTyp : isSet Typ
isSetTyp = Discrete→isSet discreteTyp

data CSort : Type ℓ-zero where
  tyS : CSort

data COp : Type ℓ-zero where
  ιOp lstOp arrOp : COp

Ar : COp → ℕ
Ar ιOp = 0
Ar lstOp = 1
Ar arrOp = 2

SortOf : (o : COp) → Fin (Ar o) → CSort
SortOf _ _ = tyS

CSig : SortedSig CSort ℓ-zero
CSig .ops = COp
CSig .arity = Ar
CSig .sortOf = SortOf
CSig .resultSort _ = tyS

CEqns : SortedEqns CSig ℓ-zero
CEqns .eqns = ⊥
CEqns .eqnSort ()
CEqns .varCount ()
CEqns .varSort ()
CEqns .lhs ()
CEqns .rhs ()

-- `Eq`-valued so matching the answer refines the operation, not just a path
decCOp : (o o' : COp) → (o Eq.≡ o') Sum.⊎ ((o Eq.≡ o') → ⊥)
decCOp ιOp ιOp = Sum.inl Eq.refl
decCOp ιOp lstOp = Sum.inr λ ()
decCOp ιOp arrOp = Sum.inr λ ()
decCOp lstOp ιOp = Sum.inr λ ()
decCOp lstOp lstOp = Sum.inl Eq.refl
decCOp lstOp arrOp = Sum.inr λ ()
decCOp arrOp ιOp = Sum.inr λ ()
decCOp arrOp lstOp = Sum.inr λ ()
decCOp arrOp arrOp = Sum.inl Eq.refl

IsIOp IsLOp IsAOp : COp → Type ℓ-zero
IsIOp ιOp = Unit
IsIOp lstOp = ⊥
IsIOp arrOp = ⊥
IsLOp ιOp = ⊥
IsLOp lstOp = Unit
IsLOp arrOp = ⊥
IsAOp ιOp = ⊥
IsAOp lstOp = ⊥
IsAOp arrOp = Unit

discreteCOp : Discrete COp
discreteCOp ιOp ιOp = yes refl
discreteCOp ιOp lstOp = no λ p → subst IsIOp p tt
discreteCOp ιOp arrOp = no λ p → subst IsIOp p tt
discreteCOp lstOp ιOp = no λ p → subst IsLOp p tt
discreteCOp lstOp lstOp = yes refl
discreteCOp lstOp arrOp = no λ p → subst IsLOp p tt
discreteCOp arrOp ιOp = no λ p → subst IsAOp p tt
discreteCOp arrOp lstOp = no λ p → subst IsAOp p tt
discreteCOp arrOp arrOp = yes refl

isSetCOp : isSet COp
isSetCOp = Discrete→isSet discreteCOp

-- The model: `Typ` itself, so that everything reduces.
Crr : CSort → Type ℓ-zero
Crr tyS = Typ

isSetCrr : (s : CSort) → isSet (Crr s)
isSetCrr tyS = isSetTyp

open import Theory.Free.Base CEqns ⊥ (λ ()) using (FreePresentation)

private
  one : {A : Type ℓX} → A → Fin 1 → A
  one a zero = a

  two : {A : Type ℓX} → A → A → Fin 2 → A
  two a b zero = a
  two a b (suc zero) = b

  cOps : Ops {σ = CSig} Crr
  cOps ιOp _ = ι
  cOps lstOp xs = lst (xs zero)
  cOps arrOp xs = xs zero ⇒ xs (suc zero)

  cSat : (e : CEqns .eqns)
    (ρ : (w : vars CEqns e) → Crr (CEqns .varSort e w))
    → TmRec Crr cOps ρ (CEqns .lhs e) ≡ TmRec Crr cOps ρ (CEqns .rhs e)
  cSat () ρ

  CModel : MOD CEqns ℓ-zero .ob
  CModel = (λ s → Crr s , isSetCrr s) , cOps , cSat

module Fold {X : CSort → Type ℓX} (α : Ops {σ = CSig} X) where

  foldT : Typ → X tyS
  foldT ι = α ιOp λ ()
  foldT (lst a) = α lstOp (one (foldT a))
  foldT (a ⇒ b) = α arrOp (two (foldT a) (foldT b))

  fold : (s : CSort) → Crr s → X s
  fold tyS = foldT

  foldOp : (o : COp) (ms : (a : Fin (Ar o)) → Crr (SortOf o a))
    → fold tyS (cOps o ms) ≡ α o (λ a → fold (SortOf o a) (ms a))
  foldOp ιOp ms = cong (α ιOp) (funExt λ ())
  foldOp lstOp ms = cong (α lstOp) (funExt λ where zero → refl)
  foldOp arrOp ms = cong (α arrOp) (funExt λ where
    zero → refl
    (suc zero) → refl)

  module _ (f : (s : CSort) → Crr s → X s)
    (homf : (o : COp) (ms : (a : Fin (Ar o)) → Crr (SortOf o a))
          → f tyS (cOps o ms) ≡ α o (λ a → f (SortOf o a) (ms a))) where

    foldUniqT : (t : Typ) → f tyS t ≡ foldT t
    foldUniqT ι = homf ιOp (λ ()) ∙ cong (α ιOp) (funExt λ ())
    foldUniqT (lst a) =
        homf lstOp (one a)
      ∙ cong (α lstOp) (funExt λ where zero → foldUniqT a)
    foldUniqT (a ⇒ b) =
        homf arrOp (two a b)
      ∙ cong (α arrOp) (funExt λ where
          zero → foldUniqT a
          (suc zero) → foldUniqT b)

    foldUniq : (s : CSort) (m : Crr s) → f s m ≡ fold s m
    foldUniq tyS = foldUniqT

cPresentation : FreePresentation ℓ-zero
cPresentation .FreePresentation.P = CModel
cPresentation .FreePresentation.satStrict () ρ
cPresentation .FreePresentation.gen ()
cPresentation .FreePresentation.rec {X = X} isSetX α sat ρ {s} = Fold.fold {X = X} α s
cPresentation .FreePresentation.recGen isSetX α sat ρ ()
cPresentation .FreePresentation.recOp {X = X} isSetX α sat ρ = Fold.foldOp {X = X} α
cPresentation .FreePresentation.recUniq {X = X} isSetX α sat ρ f homf fβ {s} =
  Fold.foldUniq {X = X} α f homf s

open import Theory.Base CEqns ⊥ (λ ()) cPresentation public
open import Theory.Type.HLevels CEqns ⊥ (λ ()) cPresentation public
open import Theory.Type.Top.Base CEqns ⊥ (λ ()) cPresentation public
open import Theory.Type.Bottom.Base CEqns ⊥ (λ ()) cPresentation public
-- the theory-level `_⇒_` is hidden: `_⇒_` here is the *type* constructor
open import Theory.Type.Function.Base CEqns ⊥ (λ ()) cPresentation public
  hiding (_⇒_)
open import Theory.Type.Sum.Base CEqns ⊥ (λ ()) cPresentation public
open import Theory.Type.Sum.Binary.Base CEqns ⊥ (λ ()) cPresentation public
open import Theory.Type.Product.Base CEqns ⊥ (λ ()) cPresentation public
open import Theory.Type.Product.Binary.Base CEqns ⊥ (λ ()) cPresentation public
open import Theory.Type.Cover.Base CEqns ⊥ (λ ()) cPresentation public
open import Theory.Type.Decidable.Base CEqns ⊥ (λ ()) cPresentation public
open import Theory.Type.Decidable.Route CEqns ⊥ (λ ()) cPresentation public
open import Theory.Combinator.Core CEqns ⊥ (λ ()) cPresentation public

pattern theElem = zero      -- lstOp: the element type
pattern theDom  = zero      -- arrOp: the domain
pattern theCod  = suc zero  -- arrOp: the codomain

-- Recovering slots from a path between whole types needs the projections,
-- not K (as in `Annotated/Guard`).
preciseC : (o : COp) → Precise o
preciseC ιOp m (ms , e) (ms' , e') =
  ΣPathP (funExt (λ ()) , isProp→PathP (λ _ → isPropModelEq) e e')
preciseC lstOp m (ms , e) (ms' , e') =
  ΣPathP (funExt slot , isProp→PathP (λ _ → isPropModelEq) e e')
  where
  whole : lst (ms zero) ≡ lst (ms' zero)
  whole = Eq.eqToPath e ∙ sym (Eq.eqToPath e')

  slot : (a : Fin 1) → ms a ≡ ms' a
  slot zero = cong elemOf whole
preciseC arrOp m (ms , e) (ms' , e') =
  ΣPathP (funExt slot , isProp→PathP (λ _ → isPropModelEq) e e')
  where
  whole : (ms zero ⇒ ms (suc zero)) ≡ (ms' zero ⇒ ms' (suc zero))
  whole = Eq.eqToPath e ∙ sym (Eq.eqToPath e')

  slot : (a : Fin 2) → ms a ≡ ms' a
  slot zero = cong domOf whole
  slot (suc zero) = cong codOf whole

headOf : Typ → COp
headOf ι = ιOp
headOf (lst _) = lstOp
headOf (_ ⇒ _) = arrOp

headOf-node : (o : COp) (ms : interpIn o ↓M) → headOf (op o ms) ≡ o
headOf-node ιOp ms = refl
headOf-node lstOp ms = refl
headOf-node arrOp ms = refl

nodeCover : Cover COp NodeAt
nodeCover .total ι _ = ιOp , ((λ ()) , Eq.refl)
nodeCover .total (lst a) _ = lstOp , (one a , Eq.refl)
nodeCover .total (a ⇒ b) _ = arrOp , (two a b , Eq.refl)
nodeCover .disjoint o o' ne m ((ms , e) , (ms' , e')) =
  Empty.rec (ne (Eq.pathToEq same))
  where
  same : o ≡ o'
  same = sym (headOf-node o ms)
       ∙ cong headOf (Eq.eqToPath e ∙ sym (Eq.eqToPath e'))
       ∙ headOf-node o' ms'

nodeAtOf : (t : Typ) → NodeAt (headOf t) t
nodeAtOf ι = (λ ()) , Eq.refl
nodeAtOf (lst a) = one a , Eq.refl
nodeAtOf (a ⇒ b) = two a b , Eq.refl

tSize : Typ → ℕ
tSize ι = 1
tSize (lst a) = suc (tSize a)
tSize (a ⇒ b) = suc (tSize a + tSize b)

private
  elem< : (a : Typ) → tSize a NO.< tSize (lst a)
  elem< a = 0 , refl

  dom< : (a b : Typ) → tSize a NO.< tSize (a ⇒ b)
  dom< a b = tSize b , (+-suc (tSize b) (tSize a)
    ∙ cong suc (+-comm (tSize b) (tSize a)))

  cod< : (a b : Typ) → tSize b NO.< tSize (a ⇒ b)
  cod< a b = tSize a , +-suc (tSize a) (tSize b)

module Subtype {X : Type ℓX} (isSetX : isSet X) (rank : X → ℕ) where

  srt : X → CSort
  srt _ = tyS

  order : LI.IPtOrder CEqns ⊥ (λ ()) cPresentation srt ℓ-zero
  order = LI.ilexOrder CEqns ⊥ (λ ()) cPresentation srt
    isSetX (λ _ → tSize) rank

  open LI.IPtOrder order using (_<_) public

  smaller : {x x' : X} {t t' : Typ}
    → tSize t' NO.< tSize t → (x' , t') < (x , t)
  smaller lt = lift (Sum.inl lt)

  callElem : {x x' : X} (a : Typ) → (x' , a) < (x , lst a)
  callElem a = smaller {t = lst a} {t' = a} (elem< a)

  callDom : {x x' : X} (a b : Typ) → (x' , a) < (x , a ⇒ b)
  callDom a b = smaller {t = a ⇒ b} {t' = a} (dom< a b)

  callCod : {x x' : X} (a b : Typ) → (x' , b) < (x , a ⇒ b)
  callCod a b = smaller {t = a ⇒ b} {t' = b} (cod< a b)
