{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Linear typing: the *same* terms, the *same* combinators, a different
   discipline.  Every variable in the context must be used exactly once.

   This is the case I expected to break the framework, because the
   multiplicative rule splits the context

     Γ₁ ⊢ f : B ⊸ A     Γ₂ ⊢ a : B
     ------------------------------  Γ = Γ₁ ⊎ Γ₂
              Γ ⊢ f a : A

   and `Γ₁`, `Γ₂` look like outputs -- which by the rule of thumb would owe
   a `Route` over the (exponentially many) splits.

   They are not outputs.  Which variables `f` consumes is a *syntactic*
   fact about `f`, so `Γ₁ = keep Γ f` is a function of the conclusion's
   context and slot zero's value -- and a slot index computed from another
   slot's value is exactly what `⊗ᴰ` is.  No search, no route.

   That is worth stating as a general fact: `⊗ᴰ`'s dependency *is* the
   leftover/threading discipline.  In the monoid framework the same idea is
   the continuation -- what the head leaves for the tail; here it is what
   the function leaves for the argument.  Same shape, different theory.

   What is genuinely out of reach is linear *inference*: if the types were
   unknown the split would stop being computable, and then it would be a
   route after all.  Checking is syntax-directed; inference is not. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Annotated.Linear where

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool
  ; if_then_else_ ; _or_ ; _and_ ; not ; false≢true)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Nat using (ℕ ; isSetℕ ; discreteℕ)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no ; Discrete)
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Annotated.Typing public
  using ( Ctx ; isSetCtx ; Jdg ; isSetIdx
        ; ArrHead ; isPropArrHead ; ArrSet ; decArrHead )
open import Theory.Instances.Annotated.Guard public

-- Which variables a term consumes.  `alam` shadows, so the binder's name
-- is not free in the abstraction.
eqB : ℕ → ℕ → Bool
eqB x y = onDec (discreteℕ x y)
  where
  onDec : Dec (x ≡ y) → Bool
  onDec (yes _) = true
  onDec (no _) = false

freeIn : ℕ → ATm → Bool
freeIn x (avar y) = eqB x y
freeIn x (aapp B f a) = freeIn x f or freeIn x a
freeIn x (alam y B t) = if eqB x y then false else freeIn x t

-- The part of `Γ` a term consumes.  This is the split, computed rather
-- than searched.
keep : Ctx → ATm → Ctx
keep [] t = []
keep ((x , A) ∷ Γ) t =
  if freeIn x t then (x , A) ∷ keep Γ t else keep Γ t

-- ...and the side condition that makes it a partition: every variable of
-- `Γ` is consumed by exactly one side.
xorB : Bool → Bool → Bool
xorB true b = not b
xorB false b = b

partitions : Ctx → ATm → ATm → Bool
partitions [] f a = true
partitions ((x , _) ∷ Γ) f a =
  xorB (freeIn x f) (freeIn x a) and partitions Γ f a

-- Contexts are discrete, so "Γ is exactly this singleton" is decidable.
discretePr : Discrete (ℕ × Ty)
discretePr (x , A) (y , B) = onParts (discreteℕ x y) (discreteTy A B)
  where
  onParts : Dec (x ≡ y) → Dec (A ≡ B) → Dec ((x , A) ≡ (y , B))
  onParts (yes p) (yes q) = yes λ i → p i , q i
  onParts (no ¬p) _ = no λ e → ¬p (cong fst e)
  onParts _ (no ¬q) = no λ e → ¬q (cong snd e)

discreteCtx : Discrete Ctx
discreteCtx [] [] = yes refl
discreteCtx [] (_ ∷ _) = no λ p → subst nilCode p tt
  where
  nilCode : Ctx → Type ℓ-zero
  nilCode [] = Unit
  nilCode (_ ∷ _) = Empty.⊥
discreteCtx (_ ∷ _) [] = no λ p → subst consCode p tt
  where
  consCode : Ctx → Type ℓ-zero
  consCode [] = Empty.⊥
  consCode (_ ∷ _) = Unit
discreteCtx (p ∷ Γ) (q ∷ Δ) = onParts (discretePr p q) (discreteCtx Γ Δ)
  where
  onParts : Dec (p ≡ q) → Dec (Γ ≡ Δ) → Dec ((p ∷ Γ) ≡ (q ∷ Δ))
  onParts (yes r) (yes s) = yes λ i → r i ∷ s i
  onParts (no ¬r) _ = no λ e → ¬r (cong hd e)
    where
    hd : Ctx → ℕ × Ty
    hd [] = p
    hd (z ∷ _) = z
  onParts _ (no ¬s) = no λ e → ¬s (cong tl e)
    where
    tl : Ctx → Ctx
    tl [] = Γ
    tl (_ ∷ Θ) = Θ

-- The judgment.  Same shape as `Der`, with linearity threaded through
-- `keep` and enforced by `partitions` at the application.
Lin : Jdg → TheoryTy ℓ-zero tm
Lin (Γ , A) (avar x) = Γ ≡ ((x , A) ∷ [])
Lin (Γ , A) (aapp B f a) =
  ((partitions Γ f a ≡ true) × Lin (keep Γ f , B ⇒ A) f)
  × Lin (keep Γ a , B) a
Lin (Γ , A) (alam x B t) = ArrHead A B × Lin ((x , B) ∷ Γ , cod A) t

isPropLin : (i : Jdg) (t : ATm) → isProp (Lin i t)
isPropLin (Γ , A) (avar x) = isSetCtx _ _
isPropLin (Γ , A) (aapp B f a) =
  isProp× (isProp× (isSetBool _ _) (isPropLin (keep Γ f , B ⇒ A) f))
          (isPropLin (keep Γ a , B) a)
isPropLin (Γ , A) (alam x B t) =
  isProp× (isPropArrHead A B) (isPropLin ((x , B) ∷ Γ , cod A) t)

LinSet : Jdg → TheorySet ℓ-zero tm
LinSet i = Lin i , λ t → isProp→isSet (isPropLin i t)

-- The two leaves, as grammars with decisions.
SingSet : Ctx → Ty → TheorySet ℓ-zero nm
SingSet Γ A =
  (λ x → Γ ≡ ((x , A) ∷ [])) , λ x → isProp→isSet (isSetCtx _ _)

decSing : (Γ : Ctx) (A : Ty) → Decidable (ty (SingSet Γ A))
decSing Γ A x _ = onEq (discreteCtx Γ ((x , A) ∷ []))
  where
  onEq : Dec (Γ ≡ ((x , A) ∷ [])) → DecTy (ty (SingSet Γ A)) x
  onEq (yes p) = Sum.inl p
  onEq (no ¬p) = Sum.inr λ p → Empty.rec (¬p p)

PartSet : Ctx → ATm → ATm → TheorySet ℓ-zero tm
PartSet Γ f a =
  (λ _ → partitions Γ f a ≡ true) , λ _ → isProp→isSet (isSetBool _ _)

decPart : (Γ : Ctx) (f a : ATm) → Decidable (ty (PartSet Γ f a))
decPart Γ f a m _ = onB (partitions Γ f a)
  where
  onB : (b : Bool) → (b ≡ true) Sum.⊎ ((b ≡ true) → ⊥Ty m)
  onB true = Sum.inl refl
  onB false = Sum.inr λ p → Empty.rec (false≢true p)

-- The rules.  `theFun`'s slot carries the partition condition alongside
-- the function's derivation, because an operation has exactly its arity
-- many slots and there is no third one to put a side condition in.
Slots : (o : AOp) → Jdg → NodeArgs ℓ-zero o
Slots varOp (Γ , A) ms theVar = SingSet Γ A
Slots (appOp B) (Γ , A) ms theFun =
  PartSet Γ (ms theFun) (ms theArg)
    &Set LinSet (keep Γ (ms theFun) , B ⇒ A)
Slots (appOp B) (Γ , A) ms theArg = LinSet (keep Γ (ms theArg) , B)
Slots (lamOp B) (Γ , A) ms theBinder = ArrSet A B
Slots (lamOp B) (Γ , A) ms theBody =
  LinSet ((ms theBinder , B) ∷ Γ , cod A)

rollNode : (o : AOp) (i : Jdg) → ⊗ᴰ o (Slots o i) ⊢ Lin i
rollNode varOp (Γ , A) m (ms , Eq.refl , ws) = ws theVar
rollNode (appOp B) (Γ , A) m (ms , Eq.refl , ws) = ws theFun , ws theArg
rollNode (lamOp B) (Γ , A) m (ms , Eq.refl , ws) = ws theBinder , ws theBody

unrollNode : (o : AOp) (i : Jdg) → Lin i & NodeAt o ⊢ ⊗ᴰ o (Slots o i)
unrollNode varOp (Γ , A) m (d , (ms , Eq.refl)) =
  node-mk {ms = ms} λ where theVar → d
unrollNode (appOp B) (Γ , A) m (d , (ms , Eq.refl)) =
  node-mk {ms = ms} λ where
    theFun → d .fst
    theArg → d .snd
unrollNode (lamOp B) (Γ , A) m (d , (ms , Eq.refl)) =
  node-mk {ms = ms} λ where
    theBinder → d .fst
    theBody → d .snd


module Check (𝒯 : AnswerFunctor) where

  open Subterm {X = Jdg} isSetIdx (λ _ → 0) hiding (_<_) public
  open Combinators 𝒯 srt order public

  step : Step LinSet
  step (Γ , A) = look nodeCover branch
    where
    nodeAns : (o : AOp) → ▷ (AnsFam LinSet) (Γ , A) & NodeAt o
      ⊢ ty (Ans (⊗ᴰSet o (Slots o (Γ , A))))
    nodeAns varOp m (β , (ms , Eq.refl)) =
      Ans-node varOp (preciseA varOp) {As = Slots varOp (Γ , A)} {ms = ms}
        λ where theVar → Ans-ofDec (ms theVar) (decSing Γ A (ms theVar) tt)
    nodeAns (appOp B) m (β , (ms , Eq.refl)) =
      Ans-node (appOp B) (preciseA (appOp B))
        {As = Slots (appOp B) (Γ , A)} {ms = ms}
        λ where
          theFun → Ans-&& (ms theFun)
            ( Ans-ofDec (ms theFun)
                (decPart Γ (ms theFun) (ms theArg) (ms theFun) tt)
            , callAt (keep Γ (ms theFun) , B ⇒ A)
                (callFun {x = Γ , A} {x' = keep Γ (ms theFun) , B ⇒ A}
                  B (ms theFun) (ms theArg)) β )
          theArg → callAt (keep Γ (ms theArg) , B)
            (callArg {x = Γ , A} {x' = keep Γ (ms theArg) , B}
              B (ms theFun) (ms theArg)) β
    nodeAns (lamOp B) m (β , (ms , Eq.refl)) =
      Ans-node (lamOp B) (preciseA (lamOp B))
        {As = Slots (lamOp B) (Γ , A)} {ms = ms}
        λ where
          theBinder → Ans-ofDec (ms theBinder) (decArrHead A B (ms theBinder) tt)
          theBody → callAt ((ms theBinder , B) ∷ Γ , cod A)
            (callBody {x = Γ , A} {x' = (ms theBinder , B) ∷ Γ , cod A}
              (ms theBinder) B (ms theBody)) β

    branch : (o : AOp)
      → ▷ (AnsFam LinSet) (Γ , A) & NodeAt o ⊢ ty (Ans (LinSet (Γ , A)))
    branch o =
      Ans-map& (rollNode o (Γ , A) ∘⊢ π₁) (unrollNode o (Γ , A))
      ∘⊢ (nodeAns o ,& π₂)

  linear : Checker LinSet
  linear = fix step
