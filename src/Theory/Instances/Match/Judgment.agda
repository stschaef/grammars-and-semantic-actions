{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Match p v = Σ[ e ∈ Env p ] (inst p e ≡ v) = fiber (inst p) v.
   Propositional since `inst p` is injective even at non-linear patterns:
   `Env` is indexed by occurrence, not by name. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Embedding using (injective→hasPropFibers)
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Match.Judgment where

open import Cubical.Data.Empty using (⊥)
import Cubical.Data.Empty as Empty
import Cubical.Data.FinData as FD
open import Cubical.Data.FinData.More using (two)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ)
open import Cubical.Data.Sigma using (_×_ ; Σ-syntax ; ΣPathP ; _,_ ; fst ; snd)
open import Cubical.Data.Sum using (_⊎_ ; isSet⊎)
import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit using (Unit ; tt ; isSetUnit ; isPropUnit)
open import Cubical.Data.W.Indexed using (IW ; node ; isOfHLevelSuc-IW)
import Cubical.Data.Equality as Eq

open import Theory.Instances.Match.Guard public

-- Patterns, external to the theory.
data Pat : Type ℓ-zero where
  pwild : Pat
  pvar : ℕ → Pat
  ptrue pfalse : Pat
  ppair : Pat → Pat → Pat

private
  PShape : Type ℓ-zero
  PShape = ℕ ⊎ ℕ

  PPos : Unit → PShape → Type ℓ-zero
  PPos _ (Sum.inl (suc (suc (suc zero)))) = FD.Fin 2
  PPos _ _ = ⊥

  PW : Unit → Type ℓ-zero
  PW = IW (λ _ → PShape) PPos (λ _ _ _ → tt)

  isSetPW : isSet (PW tt)
  isSetPW = isOfHLevelSuc-IW 1 (λ _ → isSet⊎ isSetℕ isSetℕ) tt

  toP : Pat → PW tt
  toP pwild = node (Sum.inl 0) λ ()
  toP (pvar n) = node (Sum.inr n) λ ()
  toP ptrue = node (Sum.inl 1) λ ()
  toP pfalse = node (Sum.inl 2) λ ()
  toP (ppair p q) = node (Sum.inl 3) (two (toP p) (toP q))

  fromP : PW tt → Pat
  fromP (node (Sum.inl zero) _) = pwild
  fromP (node (Sum.inl (suc zero)) _) = ptrue
  fromP (node (Sum.inl (suc (suc zero))) _) = pfalse
  fromP (node (Sum.inl (suc (suc (suc zero)))) sub) =
    ppair (fromP (sub theFst)) (fromP (sub theSnd))
  fromP (node (Sum.inl (suc (suc (suc (suc n))))) _) = pwild
  fromP (node (Sum.inr n) _) = pvar n

  patRet : (p : Pat) → fromP (toP p) ≡ p
  patRet pwild = refl
  patRet (pvar n) = refl
  patRet ptrue = refl
  patRet pfalse = refl
  patRet (ppair p q) = cong₂ ppair (patRet p) (patRet q)

isSetPat : isSet Pat
isSetPat = isOfHLevelRetract 2 toP fromP patRet isSetPW

-- One hole per occurrence; `inst` is total.
Env : Pat → Type ℓ-zero
Env pwild = Val
Env (pvar n) = Val
Env ptrue = Unit
Env pfalse = Unit
Env (ppair p q) = Env p × Env q

inst : (p : Pat) → Env p → Val
inst pwild v = v
inst (pvar n) v = v
inst ptrue _ = vtrue
inst pfalse _ = vfalse
inst (ppair p q) (e , f) = vpair (inst p e) (inst q f)

-- Stated so no unifier must invert `inst`: the pattern is an index and the
-- model element appears only on the right of `≡`.
Match : Pat → TheoryTy ℓ-zero val
Match p v = Σ[ e ∈ Env p ] (inst p e ≡ v)

instInj : (p : Pat) {e f : Env p} → inst p e ≡ inst p f → e ≡ f
instInj pwild q = q
instInj (pvar n) q = q
instInj ptrue q = refl
instInj pfalse q = refl
instInj (ppair p q) r =
  ΣPathP (instInj p (cong pairFst r) , instInj q (cong pairSnd r))

isPropMatch : (p : Pat) (v : Val) → isProp (Match p v)
isPropMatch p = injective→hasPropFibers {f = inst p} (isSetVCrr val) (instInj p)

-- No-confusion for `Val`, by recursion: a wrong head reduces to `⊥`.
HeadIs : VOp → Val → Type ℓ-zero
HeadIs vtrueOp vtrue = Unit
HeadIs vtrueOp vfalse = ⊥
HeadIs vtrueOp (vpair _ _) = ⊥
HeadIs vfalseOp vtrue = ⊥
HeadIs vfalseOp vfalse = Unit
HeadIs vfalseOp (vpair _ _) = ⊥
HeadIs vpairOp vtrue = ⊥
HeadIs vpairOp vfalse = ⊥
HeadIs vpairOp (vpair _ _) = Unit

clashTrue : (v : Val) → Match ptrue v → HeadIs vtrueOp v
clashTrue v (_ , e) = subst (HeadIs vtrueOp) e tt

clashFalse : (v : Val) → Match pfalse v → HeadIs vfalseOp v
clashFalse v (_ , e) = subst (HeadIs vfalseOp) e tt

clashPair : (p q : Pat) (v : Val) → Match (ppair p q) v → HeadIs vpairOp v
clashPair p q v (_ , e) = subst (HeadIs vpairOp) e tt

MatchSet : Pat → TheorySet ℓ-zero val
MatchSet p = Match p , λ v → isProp→isSet (isPropMatch p v)

-- One slot family per rule that has any; the nullary constants have none.
trueSlots : NodeArgs ℓ-zero vtrueOp
trueSlots vs ()

falseSlots : NodeArgs ℓ-zero vfalseOp
falseSlots vs ()

pairSlots : Pat → Pat → NodeArgs ℓ-zero vpairOp
pairSlots p q vs theFst = MatchSet p
pairSlots p q vs theSnd = MatchSet q

⊥Set : TheorySet ℓ-zero val
⊥Set = ⊥Ty , isSet⊥Ty

-- A clause list is the pointwise `⊕` of its patterns; `Dec` reads the sum
-- as a decision, `Maybe` as left-biased choice, `ND` as an enumeration.
AnySet : List Pat → TheorySet ℓ-zero val
AnySet [] = ⊥Set
AnySet (p ∷ ps) = MatchSet p ⊕Set AnySet ps

Any : List Pat → TheoryTy ℓ-zero val
Any cs = ty (AnySet cs)

module Check (𝒯 : AnswerFunctor) where

  open Subvalue {X = Pat} isSetPat (λ _ → 0) hiding (_<_) public
  open Combinators 𝒯 srt order public

  private
    Later : Pat → TheoryTy _ val
    Later = ▷ (AnsFam MatchSet)

    yes! : {p : Pat} → ((v : Val) → Match p v) → Later p ⊢ ty (Ans (MatchSet p))
    yes! h = side λ v _ → Sum.inl (h v)

  -- The refutation cannot ride in a slot (constants have none), so it
  -- rides in the hypothesis of `Ans-map&`.
  clashAt : (o : VOp) (p : Pat)
    → ((vs : interpIn o ↓M) → Match p (op o vs) → ⊥)
    → Later p & NodeAt o ⊢ ty (Ans (MatchSet p))
  clashAt o p ¬m =
    Ans-map& (λ _ (b , _) → Empty.rec* b)
             (λ where _ (d , (vs , Eq.refl)) → Empty.rec (¬m vs d))
    ∘⊢ (none {A = ⊥Set} (λ _ _ b → b) ,& π₂)

  private
    constAt : (o : VOp) (p : Pat) (As : NodeArgs ℓ-zero o)
      → ((vs : interpIn o ↓M) → (a : arities VSig o) → ty (Ans (As vs a)) (vs a))
      → (⊗ᴰ o As & NodeAt o ⊢ Match p)
      → (Match p & NodeAt o ⊢ ⊗ᴰ o As)
      → Later p & NodeAt o ⊢ ty (Ans (MatchSet p))
    constAt o p As ws roll unroll = Ans-map& roll unroll ∘⊢ (mk ,& π₂)
      where
      mk : Later p & NodeAt o ⊢ ty (Ans (⊗ᴰSet o As))
      mk _ (β , (vs , Eq.refl)) =
        Ans-node o (preciseV o) {As = As} {ms = vs} (ws vs)

    trueAt : Later ptrue & NodeAt vtrueOp ⊢ ty (Ans (MatchSet ptrue))
    trueAt = constAt vtrueOp ptrue trueSlots (λ vs ())
      (λ where _ (_ , (vs , Eq.refl)) → tt , refl)
      (λ where _ (_ , (vs , Eq.refl)) → node-mk {ms = vs} λ ())

    falseAt : Later pfalse & NodeAt vfalseOp ⊢ ty (Ans (MatchSet pfalse))
    falseAt = constAt vfalseOp pfalse falseSlots (λ vs ())
      (λ where _ (_ , (vs , Eq.refl)) → tt , refl)
      (λ where _ (_ , (vs , Eq.refl)) → node-mk {ms = vs} λ ())

    pairAt : (p q : Pat)
      → Later (ppair p q) & NodeAt vpairOp ⊢ ty (Ans (MatchSet (ppair p q)))
    pairAt p q = Ans-map& roll unroll ∘⊢ (mk ,& π₂)
      where
      mk : Later (ppair p q) & NodeAt vpairOp
         ⊢ ty (Ans (⊗ᴰSet vpairOp (pairSlots p q)))
      mk _ (β , (vs , Eq.refl)) =
        Ans-node vpairOp (preciseV vpairOp)
          {As = pairSlots p q} {ms = vs}
          λ where
            theFst → callAt p
              (callFst {x = ppair p q} {x' = p} (vs theFst) (vs theSnd)) β
            theSnd → callAt q
              (callSnd {x = ppair p q} {x' = q} (vs theFst) (vs theSnd)) β

      roll : ⊗ᴰ vpairOp (pairSlots p q) & NodeAt vpairOp ⊢ Match (ppair p q)
      roll _ ((vs , Eq.refl , ws) , _) =
        (ws theFst .fst , ws theSnd .fst) ,
        cong₂ vpair (ws theFst .snd) (ws theSnd .snd)

      unroll : Match (ppair p q) & NodeAt vpairOp ⊢ ⊗ᴰ vpairOp (pairSlots p q)
      unroll _ (d , (vs , Eq.refl)) = node-mk {ms = vs} λ where
        theFst → d .fst .fst , cong pairFst (d .snd)
        theSnd → d .fst .snd , cong pairSnd (d .snd)

  step : Step MatchSet
  step pwild = yes! λ v → v , refl
  step (pvar n) = yes! λ v → v , refl
  step ptrue = look nodeCover λ where
    vtrueOp → trueAt
    vfalseOp → clashAt vfalseOp ptrue λ vs → clashTrue (op vfalseOp vs)
    vpairOp → clashAt vpairOp ptrue λ vs → clashTrue (op vpairOp vs)
  step pfalse = look nodeCover λ where
    vtrueOp → clashAt vtrueOp pfalse λ vs → clashFalse (op vtrueOp vs)
    vfalseOp → falseAt
    vpairOp → clashAt vpairOp pfalse λ vs → clashFalse (op vpairOp vs)
  step (ppair p q) = look nodeCover λ where
    vtrueOp → clashAt vtrueOp (ppair p q) λ vs → clashPair p q (op vtrueOp vs)
    vfalseOp → clashAt vfalseOp (ppair p q) λ vs → clashPair p q (op vfalseOp vs)
    vpairOp → pairAt p q

  matched : Checker MatchSet
  matched = fix step

  matchAny : (cs : List Pat) → ⊤Ty ⊢ ty (Ans (AnySet cs))
  matchAny [] = none λ _ _ b → b
  matchAny (p ∷ ps) = matched p <|> matchAny ps
