{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- All tests are `refl`.  Unbound variables are refused by the shape mode;
   `λx. x x` by the side condition, localised to `check` returning `nothing`. -}
open import Cubical.Foundations.Prelude
module Theory.Instances.Infer.Tests where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-comm)
import Cubical.Data.Nat.Order as NO
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Empty as Empty
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Bool using (Bool ; true ; false)
import Cubical.Data.Sum as Sum

open import Theory.Instances.Infer.Elaborate
import Theory.Instances.Unify.Check as U

private variable n : ℕ

idT konst shadow nested appId selfApp openT : RawTm
idT = tlam 0 (tvar 0)
konst = tlam 0 (tlam 1 (tvar 0))
shadow = tlam 0 (tlam 0 (tvar 0))
nested = tlam 0 (tlam 1 (tapp (tvar 0) (tvar 1)))
appId = tapp idT idT
selfApp = tlam 0 (tapp (tvar 0) (tvar 0))
openT = tvar 7


-- components: unknowns left, type over them, elaborated nameless core term
inf-id : elabTy idT ≡ just (1 , fork (var zero) (var zero) , dlam (dvar 0))
inf-id = refl

inf-konst : elabTy konst
  ≡ just ( 2
         , fork (var (suc zero)) (fork (var zero) (var (suc zero)))
         , dlam (dlam (dvar 1)) )
inf-konst = refl

inf-shadow : elabTy shadow
  ≡ just ( 2
         , fork (var zero) (fork (var (suc zero)) (var (suc zero)))
         , dlam (dlam (dvar 0)) )
inf-shadow = refl

inf-nested : elabTy nested
  ≡ just ( 2
         , fork (fork (var (suc zero)) (var zero))
                (fork (var (suc zero)) (var zero))
         , dlam (dlam (dapp (dvar 1) (dvar 0))) )
inf-nested = refl

inf-appId : elabTy appId
  ≡ just ( 1
         , fork (var zero) (var zero)
         , dapp (dlam (dvar 0)) (dlam (dvar 0)) )
inf-appId = refl

-- free variable against an ambient context
openG : Goal
openG = 1 , (7 , leaf) ∷ [] , var zero , 1

inf-open : infer openG openT ≡ just (0 , leaf)
inf-open = refl


-- same source, three backends; at `ND` the answer is a singleton
inf-id-M : inferTyM idT ≡ just (1 , fork (var zero) (var zero))
inf-id-M = refl

inf-id-ND : inferTyND idT ≡ (1 , fork (var zero) (var zero)) ∷ []
inf-id-ND = refl

inf-nested-ND : inferTyND nested
  ≡ (2 , fork (fork (var (suc zero)) (var zero))
             (fork (var (suc zero)) (var zero))) ∷ []
inf-nested-ND = refl


-- refusal one: unbound variable, refused by the shape mode
no-unbound : inferTy openT ≡ nothing
no-unbound = refl

no-unbound-shape : scopeOnly (closed openT) openT ≡ nothing
no-unbound-shape = refl

-- `shapeVerdict` is total: no intrinsically typed core term erases to `tvar 7`
verdictSide : (i : Goal) → RawTm → Bool
verdictSide i t = Sum.rec (λ _ → true) (λ _ → false) (shapeVerdict i t)

no-unbound-verdict : verdictSide (closed openT) openT ≡ false
no-unbound-verdict = refl

-- `λx. x x` is well scoped; the verdict stops here
selfApp-verdict : verdictSide (closed selfApp) selfApp ≡ true
selfApp-verdict = refl


-- refusal two: `λx. x x` passes the shape mode; the whole refusal is `Sol`
selfApp-shape : scopeOnly (closed selfApp) selfApp ≡ just 1
selfApp-shape = refl

no-selfApp : inferTy selfApp ≡ nothing
no-selfApp = refl

no-selfApp-ND : inferTyND selfApp ≡ []
no-selfApp-ND = refl


-- the refusal is the occurs check, localised to `Unify/Term`'s `check`
selfApp-constraints : gen 4 [] (mvar 4 0) 1 selfApp
  ≡ (var zero , fork (var (suc zero)) (var (suc (suc zero))))
  ∷ (var (suc zero) , fork (var (suc (suc (suc zero)))) (var (suc (suc zero))))
  ∷ (var (suc zero) , var (suc (suc (suc zero))))
  ∷ []
selfApp-constraints = refl

selfApp-unsolvable : U.solve 4 (gen 4 [] (mvar 4 0) 1 selfApp) ≡ nothing
selfApp-unsolvable = refl

-- the equation the machine reaches, and the check that kills it
occurs : U.check {n = 1} zero (fork (var zero) (var (suc zero))) ≡ nothing
occurs = refl

occurs-unify : U.unifyTm 2 (var zero) (fork (var zero) (var (suc zero)))
  ≡ nothing
occurs-unify = refl

-- control: occurrence removed, `check` answers
no-occurs : U.check {n = 1} zero (fork (var (suc zero)) (var (suc zero)))
  ≡ just (fork (var zero) (var zero))
no-occurs = refl

-- self-application: Gen holds, Cor refutes — the cover's asymmetry
private
  isApp isVarT : RawTm → Type ℓ-zero
  isApp (tvar _) = Empty.⊥
  isApp (tapp _ _) = Unit
  isApp (tlam _ _) = Empty.⊥
  isVarT (tvar _) = Unit
  isVarT (tapp _ _) = Empty.⊥
  isVarT (tlam _ _) = Empty.⊥

  appFun appArg : RawTm → RawTm
  appFun (tapp f _) = f
  appFun (tvar x) = tvar x
  appFun (tlam x t) = tlam x t
  appArg (tapp _ a) = a
  appArg (tvar x) = tvar x
  appArg (tlam x t) = tlam x t

  unTvar : ℕ → RawTm → ℕ
  unTvar d (tvar x) = x
  unTvar d (tapp _ _) = d
  unTvar d (tlam _ _) = d

  tySize : Tm n → ℕ
  tySize (var _) = 1
  tySize leaf = 1
  tySize (fork a b) = suc (tySize a + tySize b)

  noSelfFork : (B A : Tm n) → B ⇛ A ≡ B → Empty.⊥
  noSelfFork B A e =
    NO.¬m<m (subst (λ z → tySize B NO.< z) (cong tySize e) lt)
    where
    lt : tySize B NO.< tySize (B ⇛ A)
    lt = NO.suc-≤-suc (tySize A , +-comm (tySize A) (tySize B))

  varCore : {m : ℕ} {Γ' : Ctx m} {A' : Tm m} (c : Core m Γ' A') (x : ℕ)
    → erase c ≡ tvar x → A' ≡ lookD Γ' x
  varCore {Γ' = Γ'} {A' = A'} (cvar y v) x e =
    subst (λ z → A' ≡ lookD Γ' z) (cong (unTvar y) e) (lookDef Γ' A' y v)
  varCore (capp f a) x e = Empty.rec (subst isVarT (sym e) tt)
  varCore (clam y b) x e = Empty.rec (subst isVarT (sym e) tt)

-- A self-application asks one context for two types at one name.
  appCore : {m : ℕ} {Γ' : Ctx m} {A' : Tm m} (c : Core m Γ' A') (x y : ℕ)
    → erase c ≡ tapp (tvar x) (tvar y) → x ≡ y → Empty.⊥
  appCore (cvar z v) x y e _ = subst isApp (sym e) tt
  appCore (clam z b) x y e _ = subst isApp (sym e) tt
  appCore {Γ' = Γ'} (capp {A = A} {B = B} f a) x y e xy =
    noSelfFork B A (ef ∙∙ cong (lookD Γ') xy ∙∙ sym ea)
    where
    ef : B ⇛ A ≡ lookD Γ' x
    ef = varCore f x (cong appFun e)

    ea : B ≡ lookD Γ' y
    ea = varCore a y (cong appArg e)


xx : RawTm
xx = tapp (tvar 0) (tvar 0)

xxCtx : Ctx 0
xxCtx = (0 , leaf) ∷ []

genXX : Gen 0 xxCtx leaf 0 xx
genXX = Sum.inl (refl , refl) , Sum.inl (refl , refl)

noCorXX : Cor xxCtx xx → Empty.⊥
noCorXX (m , Γ' , A' , c , ag , e) = appCore c 0 0 e refl
