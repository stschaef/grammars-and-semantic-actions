{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- LR parser for  E → E + T | T   T → ( E ) | x,  written with the ascent
   combinators: no table, no stack of states. -}
open import Theory.Type.SemanticAction.Testing using (_↦_ ; _at_ ; passes ; Case)
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Examples.Theory.Combinator.AscentExpr where

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)
import Cubical.Data.Maybe as MB

open import Theory.Instances.Monoid.Combinator.ExprGrammar

open import Theory.Instances.Monoid.Combinator.Incomplete.Base Tk _≟K_ ℓ-zero
  hiding (_<|>_ ; nil)
open import Theory.Instances.Monoid.Combinator.Ascent.Base Tk _≟K_
  using (module Goto ; _⟜Set_ ; _⊸Set_)
open import Theory.Instances.Monoid.Residual Tk isSetAlphabet
  using (_⊸_ ; ⊸-lam ; ⊸-app ; ⊗ε-unit-r ; ⟦⊗e⟧ ; ⟦⊗e⟧⁻)

-- The automaton.s grammar: left corners factored out, so every state
-- consumes a token before it recurses.
data SK : Type where
  sE sR sT : SK

private
  Hbr : SK → Bool → Functor ℓM SK (λ _ → tt) tt
  Hbr sE false = ‵lit ‵lp `⊗ (Var sE `⊗ (‵lit ‵rp `⊗ Var sR))
  Hbr sE true  = ‵lit ‵x `⊗ Var sR
  Hbr sR false = ‵lit ‵+ `⊗ (Var sT `⊗ Var sR)
  Hbr sR true  = k εTy
  Hbr sT false = ‵lit ‵lp `⊗ (Var sE `⊗ ‵lit ‵rp)
  Hbr sT true  = ‵lit ‵x

  H : SK → Functor ℓM SK (λ _ → tt) tt
  H x = ⊕e Bool (Hbr x)

  isSetHbr : (x : SK) (b : Bool) → isSetValued (Hbr x b)
  isSetHbr sE false =
    isSet`⊗ (isLit SK ‵lp) (isSet`⊗ (isVar SK sE)
      (isSet`⊗ (isLit SK ‵rp) (isVar SK sR)))
  isSetHbr sE true  = isSet`⊗ (isLit SK ‵x) (isVar SK sR)
  isSetHbr sR false = isSet`⊗ (isLit SK ‵+) (isSet`⊗ (isVar SK sT) (isVar SK sR))
  isSetHbr sR true  = isEps SK
  isSetHbr sT false =
    isSet`⊗ (isLit SK ‵lp) (isSet`⊗ (isVar SK sE) (isLit SK ‵rp))
  isSetHbr sT true  = isLit SK ‵x

  isSetH : (x : SK) → isSetValued (H x)
  isSetH x .fst = lift isSetBool
  isSetH x .snd = isSetHbr x

Sk : SK → TheoryTy _ tt
Sk = μ H

SkSet : SK → TheorySet _ tt
SkSet x = Sk x , isSetμ H isSetH x

private
  brSet : (x : SK) (b : Bool) → TheorySet _ tt
  brSet x b = ⟦ Hbr x b ⟧TheoryTy Sk
            , isSet⟦ Hbr x b ⟧ (isSetHbr x b) Sk (isSetμ H isSetH)

  rollH : (x : SK) → ty (brSet x false ⊕Set brSet x true) ⊢ Sk x
  rollH x = roll ∘⊢ ⊕-elim (σ⊕ false) (σ⊕ true)

open Goto MaybeAnswer MaybeCov Eset
open AFixAll (ℓF ℓM) SkSet

-- `chooseA` commits on one token of lookahead: no branch is attempted speculatively.
private
  ℓb : Level
  ℓb = ℓ-suc ℓ-zero

  mkE1 : ty (litSet ‵lp ⊗Set (SkSet sE ⊗Set (litSet ‵rp ⊗Set SkSet sR)))
       ⊢ ty (brSet sE false)
  mkE1 = ⟦⊗e⟧⁻ (‵lit ‵lp) (Var sE `⊗ (‵lit ‵rp `⊗ Var sR))
    ∘⊢ (liftTy ,⊗ (⟦⊗e⟧⁻ (Var sE) (‵lit ‵rp `⊗ Var sR)
         ∘⊢ (liftTy ,⊗ (⟦⊗e⟧⁻ (‵lit ‵rp) (Var sR) ∘⊢ (liftTy ,⊗ liftTy)))))

  mkE2 : ty (litSet ‵x ⊗Set SkSet sR) ⊢ ty (brSet sE true)
  mkE2 = ⟦⊗e⟧⁻ (‵lit ‵x) (Var sR) ∘⊢ (liftTy ,⊗ liftTy)

  mkR1 : ty (litSet ‵+ ⊗Set (SkSet sT ⊗Set SkSet sR)) ⊢ ty (brSet sR false)
  mkR1 = ⟦⊗e⟧⁻ (‵lit ‵+) (Var sT `⊗ Var sR)
    ∘⊢ (liftTy ,⊗ (⟦⊗e⟧⁻ (Var sT) (Var sR) ∘⊢ (liftTy ,⊗ liftTy)))

  mkT1 : ty (litSet ‵lp ⊗Set (SkSet sE ⊗Set litSet ‵rp)) ⊢ ty (brSet sT false)
  mkT1 = ⟦⊗e⟧⁻ (‵lit ‵lp) (Var sE `⊗ ‵lit ‵rp)
    ∘⊢ (liftTy ,⊗ (⟦⊗e⟧⁻ (Var sE) (‵lit ‵rp) ∘⊢ (liftTy ,⊗ liftTy)))

  red□ : {ℓβ : Level} {β : TheorySet ℓβ tt} {A : TheorySet ℓb tt}
       → ty β ⊢ ty A
       → Asc (ℓF ℓM) ⟨□⟩ ⟨□⟩ β ⊢ Asc (ℓF ℓM) ⟨□⟩ ⟨□⟩ A
  red□ {β = β} {A = A} = reduce {ℓB = ℓF ℓM} {a = ⟨□⟩} {c = ⟨□⟩} {β = β} {A = A}

  -- a branch led by `c` claims `c`'s class, whatever follows it
  leadCell : (c : Tk) (F : Functor ℓM SK (λ _ → tt) tt)
    → ⟦ ‵lit c `⊗ F ⟧TheoryTy Sk ⊗ ⊤Ty ⊢ Λ₁ (tk c)
  leadCell c F = (id⊢ ,⊗ ⊤Ty-intro) ∘⊢ ⊗-assoc
    ∘⊢ (((lowerTy ,⊗ id⊢) ∘⊢ ⟦⊗e⟧ {A = Sk} (‵lit c) F) ,⊗ id⊢)

  -- ...and a class with no branch claims it vacuously
  leadNone : (o : M₁) → ty (⊥Set↑ ℓb) ⊗ ⊤Ty ⊢ Λ₁ o
  leadNone o = ⊥Ty-elim ∘⊢ ⊗⊥-annihL ∘⊢ (lowerTy ,⊗ id⊢)

  CE : M₁ → TheorySet ℓb tt
  CE ε₁        = ⊥Set↑ ℓb
  CE (tk ‵x)   = brSet sE true
  CE (tk ‵+)   = ⊥Set↑ ℓb
  CE (tk ‵lp)  = brSet sE false
  CE (tk ‵rp)  = ⊥Set↑ ℓb

  CR : M₁ → TheorySet ℓb tt
  CR ε₁        = ⊥Set↑ ℓb
  CR (tk ‵x)   = ⊥Set↑ ℓb
  CR (tk ‵+)   = brSet sR false
  CR (tk ‵lp)  = ⊥Set↑ ℓb
  CR (tk ‵rp)  = ⊥Set↑ ℓb

  CT : M₁ → TheorySet ℓb tt
  CT ε₁        = ⊥Set↑ ℓb
  CT (tk ‵x)   = brSet sT true
  CT (tk ‵+)   = ⊥Set↑ ℓb
  CT (tk ‵lp)  = brSet sT false
  CT (tk ‵rp)  = ⊥Set↑ ℓb

  leadE : (o : M₁) → ty (CE o) ⊗ ⊤Ty ⊢ Λ₁ o
  leadE ε₁       = leadNone ε₁
  leadE (tk ‵x)  = leadCell ‵x (Var sR)
  leadE (tk ‵+)  = leadNone (tk ‵+)
  leadE (tk ‵lp) = leadCell ‵lp (Var sE `⊗ (‵lit ‵rp `⊗ Var sR))
  leadE (tk ‵rp) = leadNone (tk ‵rp)

  leadR : (o : M₁) → ty (CR o) ⊗ ⊤Ty ⊢ Λ₁ o
  leadR ε₁       = leadNone ε₁
  leadR (tk ‵x)  = leadNone (tk ‵x)
  leadR (tk ‵+)  = leadCell ‵+ (Var sT `⊗ Var sR)
  leadR (tk ‵lp) = leadNone (tk ‵lp)
  leadR (tk ‵rp) = leadNone (tk ‵rp)

  leadT : (o : M₁) → ty (CT o) ⊗ ⊤Ty ⊢ Λ₁ o
  leadT ε₁       = leadNone ε₁
  leadT (tk ‵x)  = lowerTy ,⊗ id⊢
  leadT (tk ‵+)  = leadNone (tk ‵+)
  leadT (tk ‵lp) = leadCell ‵lp (Var sE `⊗ ‵lit ‵rp)
  leadT (tk ‵rp) = leadNone (tk ‵rp)

  module PE = Predict CE leadE
  module PR = Predict CR leadR
  module PT = Predict CT leadT

  pE : (o : M₁) → ty (▷ Aall) ⊢ Asc (ℓF ℓM) ⟨□⟩ ⟨□⟩ (CE o)
  pE ε₁       = failA
  pE (tk ‵x)  = red□ {A = brSet sE true} mkE2 ∘⊢ amore
                  ∘⊢ goto (SkSet sR) (shift ‵x) (callAt sR)
  pE (tk ‵+)  = failA
  pE (tk ‵lp) = red□ {A = brSet sE false} mkE1 ∘⊢ amore
                  ∘⊢ goto (SkSet sE ⊗Set (litSet ‵rp ⊗Set SkSet sR)) (shift ‵lp)
                       (goto (litSet ‵rp ⊗Set SkSet sR) (amore ∘⊢ callAt sE)
                          (goto (SkSet sR) (shift ‵rp) (callAt sR)))
  pE (tk ‵rp) = failA

  pR : (o : M₁) → ty (▷ Aall) ⊢ Asc (ℓF ℓM) ⟨□⟩ ⟨□⟩ (CR o)
  pR ε₁       = failA
  pR (tk ‵x)  = failA
  pR (tk ‵+)  = red□ {A = brSet sR false} mkR1 ∘⊢ amore
                  ∘⊢ goto (SkSet sT ⊗Set SkSet sR) (shift ‵+)
                       (goto (SkSet sR) (callAt sT) (callAt sR))
  pR (tk ‵lp) = failA
  pR (tk ‵rp) = failA

  pT : (o : M₁) → ty (▷ Aall) ⊢ Asc (ℓF ℓM) ⟨□⟩ ⟨□⟩ (CT o)
  pT ε₁       = failA
  pT (tk ‵x)  = red□ {β = litSet ‵x} {A = brSet sT true} liftTy
                  ∘⊢ amore ∘⊢ shift ‵x
  pT (tk ‵+)  = failA
  pT (tk ‵lp) = red□ {A = brSet sT false} mkT1 ∘⊢ amore
                  ∘⊢ goto (SkSet sE ⊗Set litSet ‵rp) (shift ‵lp)
                       (goto (litSet ‵rp) (amore ∘⊢ callAt sE) (shift ‵rp))
  pT (tk ‵rp) = failA

  rollE : ty PE.Alt ⊢ Sk sE
  rollE = ⊕ᴰ-elim λ where
    ε₁       → ⊥Ty↑-elim
    (tk ‵x)  → roll ∘⊢ σ⊕ true
    (tk ‵+)  → ⊥Ty↑-elim
    (tk ‵lp) → roll ∘⊢ σ⊕ false
    (tk ‵rp) → ⊥Ty↑-elim

  rollR : ty (PR.Alt ⊕Set brSet sR true) ⊢ Sk sR
  rollR = ⊕-elim
    (⊕ᴰ-elim λ where
       ε₁       → ⊥Ty↑-elim
       (tk ‵x)  → ⊥Ty↑-elim
       (tk ‵+)  → roll ∘⊢ σ⊕ false
       (tk ‵lp) → ⊥Ty↑-elim
       (tk ‵rp) → ⊥Ty↑-elim)
    (roll ∘⊢ σ⊕ true)

  rollT : ty PT.Alt ⊢ Sk sT
  rollT = ⊕ᴰ-elim λ where
    ε₁       → ⊥Ty↑-elim
    (tk ‵x)  → roll ∘⊢ σ⊕ true
    (tk ‵+)  → ⊥Ty↑-elim
    (tk ‵lp) → roll ∘⊢ σ⊕ false
    (tk ‵rp) → ⊥Ty↑-elim

  step : ty (▷ Aall) ⊢ ty Aall
  step = &ᴰ-intro λ where
    sE → red□ {β = PE.Alt} {A = SkSet sE} rollE ∘⊢ PE.chooseA pE
    sR → red□ {β = PR.Alt ⊕Set brSet sR true} {A = SkSet sR} rollR
           ∘⊢ (PR.chooseA pR
                <|> (red□ {β = εSet} {A = brSet sR true} liftTy ∘⊢ nil))
    sT → red□ {β = PT.Alt} {A = SkSet sT} rollT ∘⊢ PT.chooseA pT

-- `Mot sR = E ⊸ E` is the stack of pending reductions, `⊸-app` the
-- reduction firing; hence `x + x + x` comes out left-associated.
Mot : SK → TheoryTy _ tt
Mot sE = E
Mot sR = E ⊸ E
Mot sT = Trm

private
  algH : (x : SK) → ⟦ H x ⟧TheoryTy Mot ⊢ Mot x
  algH sE = ⊕ᴰ-elim λ where
    false → ⊸-app {A = E} {C = E}
      ∘⊢ ((embE ∘⊢ parT) ,⊗ id⊢) ∘⊢ ⊗-assoc⁻ ∘⊢ (id⊢ ,⊗ ⊗-assoc⁻)
      ∘⊢ (lowerTy ,⊗ (lowerTy ,⊗ (lowerTy ,⊗ lowerTy)))
      ∘⊢ (id⊢ ,⊗ (id⊢ ,⊗ ⟦⊗e⟧ {A = Mot} (‵lit ‵rp) (Var sR)))
      ∘⊢ (id⊢ ,⊗ ⟦⊗e⟧ {A = Mot} (Var sE) (‵lit ‵rp `⊗ Var sR))
      ∘⊢ ⟦⊗e⟧ {A = Mot} (‵lit ‵lp) (Var sE `⊗ (‵lit ‵rp `⊗ Var sR))
    true → ⊸-app {A = E} {C = E}
      ∘⊢ ((embE ∘⊢ varT) ,⊗ id⊢) ∘⊢ (lowerTy ,⊗ lowerTy)
      ∘⊢ ⟦⊗e⟧ {A = Mot} (‵lit ‵x) (Var sR)
  algH sR = ⊕ᴰ-elim λ where
    false → ⊸-lam {A = E} {B = literal ‵+ ⊗ (Trm ⊗ (E ⊸ E))} {C = E}
        (⊸-app {A = E} {C = E} ∘⊢ (addE ,⊗ id⊢)
         ∘⊢ ⊗-assoc⁻ ∘⊢ (id⊢ ,⊗ ⊗-assoc⁻))
      ∘⊢ (lowerTy ,⊗ (lowerTy ,⊗ lowerTy))
      ∘⊢ (id⊢ ,⊗ ⟦⊗e⟧ {A = Mot} (Var sT) (Var sR))
      ∘⊢ ⟦⊗e⟧ {A = Mot} (‵lit ‵+) (Var sT `⊗ Var sR)
    true → ⊸-lam {A = E} {B = εTy} {C = E} ⊗ε-unit-r ∘⊢ lowerTy
  algH sT = ⊕ᴰ-elim λ where
    false → parT
      ∘⊢ (lowerTy ,⊗ (lowerTy ,⊗ lowerTy))
      ∘⊢ (id⊢ ,⊗ ⟦⊗e⟧ {A = Mot} (Var sE) (‵lit ‵rp))
      ∘⊢ ⟦⊗e⟧ {A = Mot} (‵lit ‵lp) (Var sE `⊗ ‵lit ‵rp)
    true → varT ∘⊢ lowerTy

  toOrig : (x : SK) → Sk x ⊢ Mot x
  toOrig = rec H algH

parse : Test E
parse = runA (red□ {β = SkSet sE} {A = Eset} (toOrig sE) ∘⊢ ascAt step sE)


parseExpr : String → MB.Maybe Ex
parseExpr = observe parse (semact-Maybe (λ m e → readG nE m e , tt))

-- LEFT-associated, from the left-recursive grammar, via shifts and reduces.
ascent-trees : passes
  (parseExpr at
    ( (‵x ∷ [])                       ↦ MB.just (emb var)
    ∷ (‵x ∷ ‵+ ∷ ‵x ∷ [])             ↦ MB.just (add (emb var) var)
    ∷ (‵x ∷ ‵+ ∷ ‵x ∷ ‵+ ∷ ‵x ∷ [])   ↦ MB.just (add (add (emb var) var) var)
    ∷ (‵lp ∷ ‵x ∷ ‵rp ∷ [])           ↦ MB.just (emb (par (emb var)))
    ∷ (‵lp ∷ ‵x ∷ ‵+ ∷ ‵x ∷ ‵rp ∷ ‵+ ∷ ‵x ∷ [])
        ↦ MB.just (add (emb (par (add (emb var) var))) var)
    ∷ [] ))
ascent-trees = refl

ascent-rejects : passes
  (parseExpr at
    ( []                    ↦ MB.nothing
    ∷ (‵+ ∷ [])             ↦ MB.nothing
    ∷ (‵x ∷ ‵+ ∷ [])        ↦ MB.nothing
    ∷ (‵lp ∷ ‵x ∷ [])       ↦ MB.nothing
    ∷ (‵x ∷ ‵x ∷ [])        ↦ MB.nothing
    ∷ [] ))
ascent-rejects = refl

-- LR condition, checked: branches at distinct lookahead classes never match the same word.
E-noConflict : (o o' : M₁) → (o Eq.≡ o' → Empty.⊥) → ty (CE o) & ty (CE o') ⊢ ⊥Ty
E-noConflict = PE.altDisjoint

R-noConflict : (o o' : M₁) → (o Eq.≡ o' → Empty.⊥) → ty (CR o) & ty (CR o') ⊢ ⊥Ty
R-noConflict = PR.altDisjoint

T-noConflict : (o o' : M₁) → (o Eq.≡ o' → Empty.⊥) → ty (CT o) & ty (CT o') ⊢ ⊥Ty
T-noConflict = PT.altDisjoint
