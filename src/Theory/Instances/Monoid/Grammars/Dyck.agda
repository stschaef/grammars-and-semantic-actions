{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Grammars.Dyck where

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.List using ([])
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)

-- the alphabet: one bracket pair
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

------------------------------------------------------------------------
-- The grammar as a `μ`, and the isomorphism with its unrolling.  Every
-- parser for `S` builds its step out of `rollS`/`unrollS`, so they belong
-- with the grammar rather than with any one parser.

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

  nodeIn : Node ⊢ NodeCode
  nodeIn =
    ⟦⊗e⟧⁻ _ _ ∘⊢ (liftTy ,⊗ (⟦⊗e⟧⁻ _ _ ∘⊢ (liftTy ,⊗
      (⟦⊗e⟧⁻ _ _ ∘⊢ (liftTy ,⊗ liftTy)))))

  nodeOut : NodeCode ⊢ Node
  nodeOut =
    (lowerTy ,⊗ ((lowerTy ,⊗ ((lowerTy ,⊗ lowerTy) ∘⊢ ⟦⊗e⟧ _ _)) ∘⊢ ⟦⊗e⟧ _ _))
    ∘⊢ ⟦⊗e⟧ _ _

rollS : Body ⊢ S
rollS = ⊕-elim (roll ∘⊢ σ⊕ true ∘⊢ nodeIn) (roll ∘⊢ σ⊕ false ∘⊢ liftTy)

unrollS : S ⊢ Body
unrollS = fromF ∘⊢ unroll dyckF tt
  where
  fromF : ⟦ dyckF tt ⟧TheoryTy (μ dyckF) ⊢ Body
  fromF = ⊕ᴰ-elim λ where
    true → inl ∘⊢ nodeOut
    false → inr ∘⊢ lowerTy

nilTree : S []
nilTree = (rollS ∘⊢ inr) [] εTy-pt

-- ...and the tree a parse denotes
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
