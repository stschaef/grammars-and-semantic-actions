{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.WildCat.LocallySmall.Base
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Grammars.Dyck where

open WildCatNotation

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.List using ([])
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)

data Br : Type ℓ-zero where
  lp rp : Br

_≟_ : (x y : Br) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
_≟_ lp lp = Sum.inl Eq.refl
_≟_ rp rp = Sum.inl Eq.refl
_≟_ lp rp = Sum.inr λ ()
_≟_ rp lp = Sum.inr λ ()

data Dyck : Type ℓ-zero where
  done : Dyck
  nest : Dyck → Dyck → Dyck

open import Theory.Instances.Monoid.Types Br _≟_
import Theory.Instances.Monoid.Examples Br isSetAlphabet as E
open import Theory.Instances.Monoid.Residual Br isSetAlphabet
  using (⟦⊗e⟧ ; ⟦⊗e⟧⁻)
open import Theory.Instances.Monoid.Convolution Br isSetAlphabet
  using (⟦⊗e⟧-η)
import Theory.Instances.Monoid.SemanticAction Br isSetAlphabet as SemAct

dyckBranch : Bool → Functor ℓM Unit (λ _ → tt) tt
dyckBranch = E.dyckBranch lp rp

dyckF : Unit → Functor ℓM Unit (λ _ → tt) tt
dyckF _ = E.DyckCode lp rp

isSetDyckF : (x : Unit) → isSetValued (dyckF x)
isSetDyckF _ .fst = lift isSetBool
isSetDyckF _ .snd false = lift isSetεTy
isSetDyckF _ .snd true zero = lift (isSetLiteral lp)
isSetDyckF _ .snd true (suc zero) zero = lift tt*
isSetDyckF _ .snd true (suc zero) (suc zero) zero = lift (isSetLiteral rp)
isSetDyckF _ .snd true (suc zero) (suc zero) (suc zero) = lift tt*

-- `rollS`/`unrollS` live with the grammar: every parser for `S` builds its step from them.

S : TheoryTy _ tt
S = μ dyckF tt

isSetS : isSetTheoryTy S
isSetS = isSetμ dyckF isSetDyckF tt

Node : TheoryTy _ tt
Node = literal lp ⊗ (S ⊗ (literal rp ⊗ S))

Body : TheoryTy _ tt
Body = Node ⊕ εTy

private
  NodeCode : TheoryTy _ tt
  NodeCode = ⟦ dyckBranch true ⟧TheoryTy (μ dyckF)

  -- `S → ( S ) S`: naming the proper suffixes (`afterS` = `) S`, `afterLp` = `S ) S`,
  -- as the parsers do) lets the round-trip proof peel one level at a time
  afterS : TheoryTy _ tt
  afterS = literal rp ⊗ S

  afterLp : TheoryTy _ tt
  afterLp = S ⊗ afterS

  afterSBranch afterLpBranch : Functor ℓM Unit (λ _ → tt) tt
  afterSBranch = ⊗e _⊙_ (two (k (literal rp)) (Var tt))
  afterLpBranch = ⊗e _⊙_ (two (Var tt) afterSBranch)

  afterSCode afterLpCode : TheoryTy _ tt
  afterSCode = ⟦ afterSBranch ⟧TheoryTy (μ dyckF)
  afterLpCode = ⟦ afterLpBranch ⟧TheoryTy (μ dyckF)

  afterSIn : afterS ⊢ afterSCode
  afterSIn = ⟦⊗e⟧⁻ _ _ ∘⊢ (liftTy ,⊗ liftTy)

  afterSOut : afterSCode ⊢ afterS
  afterSOut = (lowerTy ,⊗ lowerTy) ∘⊢ ⟦⊗e⟧ _ _

  afterLpIn : afterLp ⊢ afterLpCode
  afterLpIn = ⟦⊗e⟧⁻ _ _ ∘⊢ (liftTy ,⊗ afterSIn)

  afterLpOut : afterLpCode ⊢ afterLp
  afterLpOut = (lowerTy ,⊗ afterSOut) ∘⊢ ⟦⊗e⟧ _ _

  nodeIn : Node ⊢ NodeCode
  nodeIn = ⟦⊗e⟧⁻ _ _ ∘⊢ (liftTy ,⊗ afterLpIn)

  nodeOut : NodeCode ⊢ Node
  nodeOut = (lowerTy ,⊗ afterLpOut) ∘⊢ ⟦⊗e⟧ _ _

  -- one direction is `refl` (slots built slotwise); the other is `⟦⊗e⟧-η` per nesting level
  nodeOut∘nodeIn : nodeOut ∘⊢ nodeIn ≡ id⊢
  nodeOut∘nodeIn = refl

  afterSIn∘Out : afterSIn ∘⊢ afterSOut ≡ id⊢
  afterSIn∘Out = ⟦⊗e⟧-η (k (literal rp)) (Var tt)

  afterLpIn∘Out : afterLpIn ∘⊢ afterLpOut ≡ id⊢
  afterLpIn∘Out =
    cong (λ (z : afterSCode ⊢ afterSCode) →
            ⟦⊗e⟧⁻ (Var tt) afterSBranch ∘⊢ (id⊢ ,⊗ z)
            ∘⊢ ⟦⊗e⟧ (Var tt) afterSBranch)
         afterSIn∘Out
    ∙ ⟦⊗e⟧-η (Var tt) afterSBranch

  nodeIn∘nodeOut : nodeIn ∘⊢ nodeOut ≡ id⊢
  nodeIn∘nodeOut =
    cong (λ (z : afterLpCode ⊢ afterLpCode) →
            ⟦⊗e⟧⁻ (k (literal lp)) afterLpBranch ∘⊢ (id⊢ ,⊗ z)
            ∘⊢ ⟦⊗e⟧ (k (literal lp)) afterLpBranch)
         afterLpIn∘Out
    ∙ ⟦⊗e⟧-η (k (literal lp)) afterLpBranch

rollS : Body ⊢ S
rollS = ⊕-elim (roll ∘⊢ σ⊕ true ∘⊢ nodeIn) (roll ∘⊢ σ⊕ false ∘⊢ liftTy)

unrollS : S ⊢ Body
unrollS = fromF ∘⊢ unroll dyckF tt
  where
  fromF : ⟦ dyckF tt ⟧TheoryTy (μ dyckF) ⊢ Body
  fromF = ⊕ᴰ-elim λ where
    true → inl ∘⊢ nodeOut
    false → inr ∘⊢ lowerTy

rollS∘unrollS : rollS ∘⊢ unrollS ≡ id⊢
rollS∘unrollS = funExt λ m → funExt λ where
  (roll .m (true , z)) i → roll m (true , funExt⁻ (funExt⁻ nodeIn∘nodeOut m) z i)
  (roll .m (false , z)) → refl

unrollS∘rollS : unrollS ∘⊢ rollS ≡ id⊢
unrollS∘rollS = funExt λ m → funExt λ where
  (Sum.inl x) → refl
  (Sum.inr y) → refl

rollS≅ : Body ≅ S
rollS≅ .WildCatIso.fun = rollS
rollS≅ .WildCatIso.inv = unrollS
rollS≅ .WildCatIso.sec = rollS∘unrollS
rollS≅ .WildCatIso.ret = unrollS∘rollS

nilTree : S []
nilTree = (rollS ∘⊢ inr) [] εTy-pt

semactS : SemanticAction S Dyck
semactS = semact-rec alg tt
  where
  ΔD : Unit → TheoryTy ℓ-zero tt
  ΔD _ = SemAct.Δ Dyck

  nodeVal : ⟦ dyckBranch true ⟧TheoryTy ΔD ⊢ SemAct.Δ Dyck
  nodeVal m (ms , e , xs) =
    nest (xs (suc zero) .snd .snd zero .lower .fst)
         (xs (suc zero) .snd .snd (suc zero) .snd .snd (suc zero) .lower .fst)
    , tt

  alg : (x : Unit) → ⟦ dyckF x ⟧TheoryTy ΔD ⊢ ΔD x
  alg _ = ⊕ᴰ-elim λ where
    true → nodeVal
    false → semact-pure done
